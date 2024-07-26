# Connected components of universes

```agda
module foundation.connected-components-universesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subuniversesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Theᵉ **connectedᵉ component**ᵉ ofᵉ aᵉ universeᵉ `UUᵉ l`ᵉ atᵉ aᵉ typeᵉ `Aᵉ : UUᵉ l`ᵉ isᵉ theᵉ
typeᵉ ofᵉ allᵉ `Xᵉ : UUᵉ l`ᵉ thatᵉ areᵉ
[merelyᵉ equivalent](foundation.mere-equivalences.mdᵉ) to `A`.ᵉ Moreᵉ generally,ᵉ weᵉ
defineᵉ theᵉ componentᵉ ofᵉ aᵉ universeᵉ `UUᵉ l1`ᵉ ofᵉ typesᵉ
[merelyᵉ equal](foundation.mere-equality.mdᵉ) to `Aᵉ : UUᵉ l2`.ᵉ

## Definition

### The connected component of a universe with variable universe

```agda
component-UU-Levelᵉ :
  (l1ᵉ : Level) {l2ᵉ : Level} (Aᵉ : UUᵉ l2ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
component-UU-Levelᵉ l1ᵉ Aᵉ = type-subtypeᵉ (mere-equiv-Propᵉ {l2ᵉ = l1ᵉ} Aᵉ)

type-component-UU-Levelᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} → component-UU-Levelᵉ l1ᵉ Aᵉ → UUᵉ l1ᵉ
type-component-UU-Levelᵉ Xᵉ = pr1ᵉ Xᵉ

abstract
  mere-equiv-component-UU-Levelᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} (Xᵉ : component-UU-Levelᵉ l1ᵉ Aᵉ) →
    mere-equivᵉ Aᵉ (type-component-UU-Levelᵉ Xᵉ)
  mere-equiv-component-UU-Levelᵉ Xᵉ = pr2ᵉ Xᵉ
```

### The connected component of a universe

```agda
component-UUᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (lsuc l1ᵉ)
component-UUᵉ {l1ᵉ} Aᵉ = component-UU-Levelᵉ l1ᵉ Aᵉ

type-component-UUᵉ : {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : component-UUᵉ Aᵉ) → UUᵉ l1ᵉ
type-component-UUᵉ Xᵉ = type-component-UU-Levelᵉ Xᵉ

abstract
  mere-equiv-component-UUᵉ :
    {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : component-UUᵉ Aᵉ) →
    mere-equivᵉ Aᵉ (type-component-UUᵉ Xᵉ)
  mere-equiv-component-UUᵉ Xᵉ = mere-equiv-component-UU-Levelᵉ Xᵉ
```

## Properties

### Characterization of the identity types of `component-UU`

```agda
equiv-component-UU-Levelᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} (Xᵉ Yᵉ : component-UU-Levelᵉ l1ᵉ Aᵉ) → UUᵉ l1ᵉ
equiv-component-UU-Levelᵉ Xᵉ Yᵉ =
  type-component-UU-Levelᵉ Xᵉ ≃ᵉ type-component-UU-Levelᵉ Yᵉ

id-equiv-component-UU-Levelᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} (Xᵉ : component-UU-Levelᵉ l1ᵉ Aᵉ) →
  equiv-component-UU-Levelᵉ Xᵉ Xᵉ
id-equiv-component-UU-Levelᵉ Xᵉ = id-equivᵉ

equiv-eq-component-UU-Levelᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} {Xᵉ Yᵉ : component-UU-Levelᵉ l1ᵉ Aᵉ} →
  Xᵉ ＝ᵉ Yᵉ → equiv-component-UU-Levelᵉ Xᵉ Yᵉ
equiv-eq-component-UU-Levelᵉ {Xᵉ = Xᵉ} reflᵉ =
  id-equiv-component-UU-Levelᵉ Xᵉ

abstract
  is-torsorial-equiv-component-UU-Levelᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} (Xᵉ : component-UU-Levelᵉ l1ᵉ Aᵉ) →
    is-torsorialᵉ (equiv-component-UU-Levelᵉ Xᵉ)
  is-torsorial-equiv-component-UU-Levelᵉ Xᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-equivᵉ (type-component-UU-Levelᵉ Xᵉ))
      ( λ Yᵉ → is-prop-mere-equivᵉ _ Yᵉ)
      ( type-component-UU-Levelᵉ Xᵉ)
      ( id-equivᵉ)
      ( mere-equiv-component-UU-Levelᵉ Xᵉ)

abstract
  is-equiv-equiv-eq-component-UU-Levelᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} (Xᵉ Yᵉ : component-UU-Levelᵉ l1ᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-component-UU-Levelᵉ {Xᵉ = Xᵉ} {Yᵉ})
  is-equiv-equiv-eq-component-UU-Levelᵉ Xᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-component-UU-Levelᵉ Xᵉ)
      ( λ Yᵉ → equiv-eq-component-UU-Levelᵉ {Xᵉ = Xᵉ} {Yᵉ})

eq-equiv-component-UU-Levelᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} (Xᵉ Yᵉ : component-UU-Levelᵉ l1ᵉ Aᵉ) →
  equiv-component-UU-Levelᵉ Xᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
eq-equiv-component-UU-Levelᵉ Xᵉ Yᵉ =
  map-inv-is-equivᵉ (is-equiv-equiv-eq-component-UU-Levelᵉ Xᵉ Yᵉ)

equiv-component-UUᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ Yᵉ : component-UUᵉ Aᵉ) → UUᵉ l1ᵉ
equiv-component-UUᵉ Xᵉ Yᵉ = equiv-component-UU-Levelᵉ Xᵉ Yᵉ

id-equiv-component-UUᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : component-UUᵉ Aᵉ) → equiv-component-UUᵉ Xᵉ Xᵉ
id-equiv-component-UUᵉ Xᵉ = id-equiv-component-UU-Levelᵉ Xᵉ

equiv-eq-component-UUᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Xᵉ Yᵉ : component-UUᵉ Aᵉ} →
  Xᵉ ＝ᵉ Yᵉ → equiv-component-UUᵉ Xᵉ Yᵉ
equiv-eq-component-UUᵉ pᵉ = equiv-eq-component-UU-Levelᵉ pᵉ

abstract
  is-torsorial-equiv-component-UUᵉ :
    {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : component-UUᵉ Aᵉ) →
    is-torsorialᵉ (equiv-component-UUᵉ Xᵉ)
  is-torsorial-equiv-component-UUᵉ Xᵉ =
    is-torsorial-equiv-component-UU-Levelᵉ Xᵉ

abstract
  is-equiv-equiv-eq-component-UUᵉ :
    {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ Yᵉ : component-UUᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-component-UUᵉ {Xᵉ = Xᵉ} {Yᵉ})
  is-equiv-equiv-eq-component-UUᵉ Xᵉ Yᵉ =
    is-equiv-equiv-eq-component-UU-Levelᵉ Xᵉ Yᵉ

eq-equiv-component-UUᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ Yᵉ : component-UUᵉ Aᵉ) →
  equiv-component-UUᵉ Xᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
eq-equiv-component-UUᵉ Xᵉ Yᵉ =
  eq-equiv-component-UU-Levelᵉ Xᵉ Yᵉ
```

```agda
abstract
  is-contr-component-UU-Level-emptyᵉ :
    (lᵉ : Level) → is-contrᵉ (component-UU-Levelᵉ lᵉ emptyᵉ)
  pr1ᵉ (pr1ᵉ (is-contr-component-UU-Level-emptyᵉ lᵉ)) = raise-emptyᵉ lᵉ
  pr2ᵉ (pr1ᵉ (is-contr-component-UU-Level-emptyᵉ lᵉ)) =
    unit-trunc-Propᵉ (compute-raiseᵉ lᵉ emptyᵉ)
  pr2ᵉ (is-contr-component-UU-Level-emptyᵉ lᵉ) Xᵉ =
    eq-equiv-subuniverseᵉ
      ( mere-equiv-Propᵉ emptyᵉ)
      ( equiv-is-emptyᵉ
        ( map-inv-equivᵉ (compute-raiseᵉ lᵉ emptyᵉ))
        ( λ xᵉ →
          apply-universal-property-trunc-Propᵉ
          ( pr2ᵉ Xᵉ)
          ( empty-Propᵉ)
          ( λ eᵉ → map-inv-equivᵉ eᵉ xᵉ)))

abstract
  is-contr-component-UU-emptyᵉ : is-contrᵉ (component-UUᵉ emptyᵉ)
  is-contr-component-UU-emptyᵉ =
    is-contr-component-UU-Level-emptyᵉ lzero
```

### The connected components of universes are `0`-connected

```agda
abstract
  is-0-connected-component-UUᵉ :
    {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-0-connectedᵉ (component-UUᵉ Xᵉ)
  is-0-connected-component-UUᵉ Xᵉ =
    is-0-connected-mere-eqᵉ
      ( pairᵉ Xᵉ (refl-mere-equivᵉ Xᵉ))
      ( λ Yᵉ →
        map-trunc-Propᵉ
          ( eq-equiv-component-UUᵉ (pairᵉ Xᵉ (refl-mere-equivᵉ Xᵉ)) Yᵉ)
          ( mere-equiv-component-UUᵉ Yᵉ))
```