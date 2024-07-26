# Small types

```agda
module foundation-core.small-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ saidᵉ to beᵉ **small**ᵉ with respectᵉ to aᵉ universeᵉ `UUᵉ l`ᵉ ifᵉ itᵉ isᵉ
[equivalent](foundation-core.equivalences.mdᵉ) to aᵉ typeᵉ in `UUᵉ l`.ᵉ

## Definitions

### Small types

```agda
is-smallᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
is-smallᵉ lᵉ Aᵉ = Σᵉ (UUᵉ lᵉ) (λ Xᵉ → Aᵉ ≃ᵉ Xᵉ)

module _
  {lᵉ l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Hᵉ : is-smallᵉ lᵉ Aᵉ)
  where

  type-is-smallᵉ : UUᵉ lᵉ
  type-is-smallᵉ = pr1ᵉ Hᵉ

  equiv-is-smallᵉ : Aᵉ ≃ᵉ type-is-smallᵉ
  equiv-is-smallᵉ = pr2ᵉ Hᵉ

  inv-equiv-is-smallᵉ : type-is-smallᵉ ≃ᵉ Aᵉ
  inv-equiv-is-smallᵉ = inv-equivᵉ equiv-is-smallᵉ

  map-equiv-is-smallᵉ : Aᵉ → type-is-smallᵉ
  map-equiv-is-smallᵉ = map-equivᵉ equiv-is-smallᵉ

  map-inv-equiv-is-smallᵉ : type-is-smallᵉ → Aᵉ
  map-inv-equiv-is-smallᵉ = map-inv-equivᵉ equiv-is-smallᵉ
```

### The subuniverse of `UU l1`-small types in `UU l2`

```agda
Small-Typeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Small-Typeᵉ l1ᵉ l2ᵉ = Σᵉ (UUᵉ l2ᵉ) (is-smallᵉ l1ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Small-Typeᵉ l1ᵉ l2ᵉ)
  where

  type-Small-Typeᵉ : UUᵉ l2ᵉ
  type-Small-Typeᵉ = pr1ᵉ Aᵉ

  is-small-type-Small-Typeᵉ : is-smallᵉ l1ᵉ type-Small-Typeᵉ
  is-small-type-Small-Typeᵉ = pr2ᵉ Aᵉ

  small-type-Small-Typeᵉ : UUᵉ l1ᵉ
  small-type-Small-Typeᵉ = type-is-smallᵉ is-small-type-Small-Typeᵉ

  equiv-is-small-type-Small-Typeᵉ :
    type-Small-Typeᵉ ≃ᵉ small-type-Small-Typeᵉ
  equiv-is-small-type-Small-Typeᵉ =
    equiv-is-smallᵉ is-small-type-Small-Typeᵉ
```

## Properties

### Being small is a property

```agda
is-prop-is-smallᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → is-propᵉ (is-smallᵉ lᵉ Aᵉ)
is-prop-is-smallᵉ lᵉ Aᵉ =
  is-prop-is-proof-irrelevantᵉ
    ( λ Xeᵉ →
      is-contr-equiv'ᵉ
        ( Σᵉ (UUᵉ lᵉ) (λ Yᵉ → (pr1ᵉ Xeᵉ) ≃ᵉ Yᵉ))
        ( equiv-totᵉ ((λ Yᵉ → equiv-precomp-equivᵉ (pr2ᵉ Xeᵉ) Yᵉ)))
        ( is-torsorial-equivᵉ (pr1ᵉ Xeᵉ)))

is-small-Propᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → Propᵉ (lsuc lᵉ ⊔ l1ᵉ)
pr1ᵉ (is-small-Propᵉ lᵉ Aᵉ) = is-smallᵉ lᵉ Aᵉ
pr2ᵉ (is-small-Propᵉ lᵉ Aᵉ) = is-prop-is-smallᵉ lᵉ Aᵉ
```

### Any type in `UU l1` is `l1`-small

```agda
is-small'ᵉ : {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-smallᵉ l1ᵉ Aᵉ
pr1ᵉ (is-small'ᵉ {Aᵉ = Aᵉ}) = Aᵉ
pr2ᵉ is-small'ᵉ = id-equivᵉ
```

### Every type of universe level `l1` is `l1 ⊔ l2`-small

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Xᵉ : UUᵉ l1ᵉ)
  where

  is-small-lmaxᵉ : is-smallᵉ (l1ᵉ ⊔ l2ᵉ) Xᵉ
  pr1ᵉ is-small-lmaxᵉ = raiseᵉ l2ᵉ Xᵉ
  pr2ᵉ is-small-lmaxᵉ = compute-raiseᵉ l2ᵉ Xᵉ

  is-contr-is-small-lmaxᵉ :
    is-contrᵉ (is-smallᵉ (l1ᵉ ⊔ l2ᵉ) Xᵉ)
  pr1ᵉ is-contr-is-small-lmaxᵉ = is-small-lmaxᵉ
  pr2ᵉ is-contr-is-small-lmaxᵉ xᵉ = eq-is-propᵉ (is-prop-is-smallᵉ (l1ᵉ ⊔ l2ᵉ) Xᵉ)
```

### Every type of universe level `l` is `UU (lsuc l)`-small

```agda
is-small-lsucᵉ : {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-smallᵉ (lsuc lᵉ) Xᵉ
is-small-lsucᵉ {lᵉ} Xᵉ = is-small-lmaxᵉ (lsuc lᵉ) Xᵉ
```

### Small types are closed under equivalences

```agda
is-small-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : UUᵉ l2ᵉ) →
  Aᵉ ≃ᵉ Bᵉ → is-smallᵉ l3ᵉ Bᵉ → is-smallᵉ l3ᵉ Aᵉ
pr1ᵉ (is-small-equivᵉ Bᵉ eᵉ (Xᵉ ,ᵉ hᵉ)) = Xᵉ
pr2ᵉ (is-small-equivᵉ Bᵉ eᵉ (Xᵉ ,ᵉ hᵉ)) = hᵉ ∘eᵉ eᵉ

is-small-equiv'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) {Bᵉ : UUᵉ l2ᵉ} →
  Aᵉ ≃ᵉ Bᵉ → is-smallᵉ l3ᵉ Aᵉ → is-smallᵉ l3ᵉ Bᵉ
is-small-equiv'ᵉ Aᵉ eᵉ = is-small-equivᵉ Aᵉ (inv-equivᵉ eᵉ)

equiv-is-small-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  Aᵉ ≃ᵉ Bᵉ → is-smallᵉ l3ᵉ Aᵉ ≃ᵉ is-smallᵉ l3ᵉ Bᵉ
equiv-is-small-equivᵉ eᵉ =
  equiv-totᵉ (equiv-precomp-equivᵉ (inv-equivᵉ eᵉ))
```

### The universe of `UU l1`-small types in `UU l2` is equivalent to the universe of `UU l2`-small types in `UU l1`

```agda
equiv-Small-Typeᵉ :
  (l1ᵉ l2ᵉ : Level) → Small-Typeᵉ l1ᵉ l2ᵉ ≃ᵉ Small-Typeᵉ l2ᵉ l1ᵉ
equiv-Small-Typeᵉ l1ᵉ l2ᵉ =
  ( equiv-totᵉ (λ Xᵉ → equiv-totᵉ (λ Yᵉ → equiv-inv-equivᵉ))) ∘eᵉ
  ( equiv-left-swap-Σᵉ)
```

### Being small is closed under mere equivalences

```agda
is-small-mere-equivᵉ :
  (lᵉ : Level) {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → mere-equivᵉ Aᵉ Bᵉ →
  is-smallᵉ lᵉ Bᵉ → is-smallᵉ lᵉ Aᵉ
is-small-mere-equivᵉ lᵉ eᵉ Hᵉ =
  apply-universal-property-trunc-Propᵉ eᵉ
    ( is-small-Propᵉ lᵉ _)
    ( λ e'ᵉ → is-small-equivᵉ _ e'ᵉ Hᵉ)
```

### Any contractible type is small

```agda
is-small-is-contrᵉ :
  (lᵉ : Level) {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-contrᵉ Aᵉ → is-smallᵉ lᵉ Aᵉ
pr1ᵉ (is-small-is-contrᵉ lᵉ Hᵉ) = raise-unitᵉ lᵉ
pr2ᵉ (is-small-is-contrᵉ lᵉ Hᵉ) = equiv-is-contrᵉ Hᵉ is-contr-raise-unitᵉ
```

### The unit type is small with respect to any universe

```agda
is-small-unitᵉ : {lᵉ : Level} → is-smallᵉ lᵉ unitᵉ
is-small-unitᵉ = is-small-is-contrᵉ _ is-contr-unitᵉ
```

### Small types are closed under dependent pair types

```agda
is-small-Σᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  is-smallᵉ l3ᵉ Aᵉ → ((xᵉ : Aᵉ) → is-smallᵉ l4ᵉ (Bᵉ xᵉ)) → is-smallᵉ (l3ᵉ ⊔ l4ᵉ) (Σᵉ Aᵉ Bᵉ)
pr1ᵉ (is-small-Σᵉ {Bᵉ = Bᵉ} (Xᵉ ,ᵉ eᵉ) Hᵉ) =
  Σᵉ Xᵉ (λ xᵉ → pr1ᵉ (Hᵉ (map-inv-equivᵉ eᵉ xᵉ)))
pr2ᵉ (is-small-Σᵉ {Bᵉ = Bᵉ} (Xᵉ ,ᵉ eᵉ) Hᵉ) =
  equiv-Σᵉ
    ( λ xᵉ → pr1ᵉ (Hᵉ (map-inv-equivᵉ eᵉ xᵉ)))
    ( eᵉ)
    ( λ aᵉ →
      ( equiv-trᵉ
        ( λ tᵉ → pr1ᵉ (Hᵉ tᵉ))
        ( invᵉ (is-retraction-map-inv-equivᵉ eᵉ aᵉ))) ∘eᵉ
      ( pr2ᵉ (Hᵉ aᵉ)))

Σ-Small-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Small-Typeᵉ l1ᵉ l2ᵉ) →
  (Bᵉ : type-Small-Typeᵉ Aᵉ → Small-Typeᵉ l3ᵉ l4ᵉ) → Small-Typeᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
pr1ᵉ (Σ-Small-Typeᵉ Aᵉ Bᵉ) = Σᵉ (type-Small-Typeᵉ Aᵉ) (λ aᵉ → type-Small-Typeᵉ (Bᵉ aᵉ))
pr2ᵉ (Σ-Small-Typeᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} {l4ᵉ} Aᵉ Bᵉ) =
  is-small-Σᵉ (is-small-type-Small-Typeᵉ Aᵉ) (λ aᵉ → is-small-type-Small-Typeᵉ (Bᵉ aᵉ))
```

### Small types are closed under cartesian products

```agda
is-small-productᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-smallᵉ l3ᵉ Aᵉ → is-smallᵉ l4ᵉ Bᵉ → is-smallᵉ (l3ᵉ ⊔ l4ᵉ) (Aᵉ ×ᵉ Bᵉ)
is-small-productᵉ Hᵉ Kᵉ = is-small-Σᵉ Hᵉ (λ aᵉ → Kᵉ)

product-Small-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} →
  Small-Typeᵉ l1ᵉ l2ᵉ → Small-Typeᵉ l3ᵉ l4ᵉ → Small-Typeᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
pr1ᵉ (product-Small-Typeᵉ Aᵉ Bᵉ) = type-Small-Typeᵉ Aᵉ ×ᵉ type-Small-Typeᵉ Bᵉ
pr2ᵉ (product-Small-Typeᵉ Aᵉ Bᵉ) =
  is-small-productᵉ (is-small-type-Small-Typeᵉ Aᵉ) (is-small-type-Small-Typeᵉ Bᵉ)
```

### Any product of small types indexed by a small type is small

```agda
is-small-Πᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  is-smallᵉ l3ᵉ Aᵉ → ((xᵉ : Aᵉ) → is-smallᵉ l4ᵉ (Bᵉ xᵉ)) →
  is-smallᵉ (l3ᵉ ⊔ l4ᵉ) ((xᵉ : Aᵉ) → Bᵉ xᵉ)
pr1ᵉ (is-small-Πᵉ {Bᵉ = Bᵉ} (Xᵉ ,ᵉ eᵉ) Hᵉ) =
  (xᵉ : Xᵉ) → pr1ᵉ (Hᵉ (map-inv-equivᵉ eᵉ xᵉ))
pr2ᵉ (is-small-Πᵉ {Bᵉ = Bᵉ} (Xᵉ ,ᵉ eᵉ) Hᵉ) =
  equiv-Πᵉ
    ( λ (xᵉ : Xᵉ) → pr1ᵉ (Hᵉ (map-inv-equivᵉ eᵉ xᵉ)))
    ( eᵉ)
    ( λ aᵉ →
      ( equiv-trᵉ
      ( λ tᵉ → pr1ᵉ (Hᵉ tᵉ))
        ( invᵉ (is-retraction-map-inv-equivᵉ eᵉ aᵉ))) ∘eᵉ
      ( pr2ᵉ (Hᵉ aᵉ)))

Π-Small-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Small-Typeᵉ l1ᵉ l2ᵉ) →
  (type-Small-Typeᵉ Aᵉ → Small-Typeᵉ l3ᵉ l4ᵉ) → Small-Typeᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
pr1ᵉ (Π-Small-Typeᵉ Aᵉ Bᵉ) = (aᵉ : type-Small-Typeᵉ Aᵉ) → type-Small-Typeᵉ (Bᵉ aᵉ)
pr2ᵉ (Π-Small-Typeᵉ Aᵉ Bᵉ) =
  is-small-Πᵉ (is-small-type-Small-Typeᵉ Aᵉ) (λ aᵉ → is-small-type-Small-Typeᵉ (Bᵉ aᵉ))
```

### Small types are closed under function types

```agda
is-small-function-typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-smallᵉ l3ᵉ Aᵉ → is-smallᵉ l4ᵉ Bᵉ → is-smallᵉ (l3ᵉ ⊔ l4ᵉ) (Aᵉ → Bᵉ)
is-small-function-typeᵉ Hᵉ Kᵉ = is-small-Πᵉ Hᵉ (λ aᵉ → Kᵉ)
```

### Small types are closed under coproduct types

```agda
is-small-coproductᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-smallᵉ l3ᵉ Aᵉ → is-smallᵉ l4ᵉ Bᵉ → is-smallᵉ (l3ᵉ ⊔ l4ᵉ) (Aᵉ +ᵉ Bᵉ)
pr1ᵉ (is-small-coproductᵉ Hᵉ Kᵉ) = type-is-smallᵉ Hᵉ +ᵉ type-is-smallᵉ Kᵉ
pr2ᵉ (is-small-coproductᵉ Hᵉ Kᵉ) =
  equiv-coproductᵉ (equiv-is-smallᵉ Hᵉ) (equiv-is-smallᵉ Kᵉ)

coproduct-Small-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} →
  Small-Typeᵉ l1ᵉ l2ᵉ → Small-Typeᵉ l3ᵉ l4ᵉ → Small-Typeᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
pr1ᵉ (coproduct-Small-Typeᵉ Aᵉ Bᵉ) = type-Small-Typeᵉ Aᵉ +ᵉ type-Small-Typeᵉ Bᵉ
pr2ᵉ (coproduct-Small-Typeᵉ Aᵉ Bᵉ) =
  is-small-coproductᵉ (is-small-type-Small-Typeᵉ Aᵉ) (is-small-type-Small-Typeᵉ Bᵉ)
```

### The type of logical equivalences between small types is small

```agda
is-small-logical-equivalenceᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-smallᵉ l3ᵉ Aᵉ → is-smallᵉ l4ᵉ Bᵉ → is-smallᵉ (l3ᵉ ⊔ l4ᵉ) (Aᵉ ↔ᵉ Bᵉ)
is-small-logical-equivalenceᵉ Hᵉ Kᵉ =
  is-small-productᵉ (is-small-function-typeᵉ Hᵉ Kᵉ) (is-small-function-typeᵉ Kᵉ Hᵉ)
```

## See also

-ᵉ [Smallᵉ maps](foundation.small-maps.mdᵉ)