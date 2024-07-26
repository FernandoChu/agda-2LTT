# Torsorial type families

```agda
module foundation.torsorial-type-familiesᵉ where

open import foundation-core.torsorial-type-familiesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.universal-property-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Idea

Aᵉ typeᵉ familyᵉ `E`ᵉ overᵉ `B`ᵉ isᵉ saidᵉ to beᵉ **torsorial**ᵉ ifᵉ itsᵉ
[totalᵉ space](foundation.dependent-pair-types.mdᵉ) isᵉ
[contractible](foundation.contractible-types.md).ᵉ Byᵉ theᵉ
[fundamentalᵉ theoremᵉ ofᵉ identityᵉ types](foundation.fundamental-theorem-of-identity-types.mdᵉ)
itᵉ followsᵉ thatᵉ aᵉ typeᵉ familyᵉ `E`ᵉ isᵉ torsorialᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ in theᵉ
[image](foundation.images.mdᵉ) ofᵉ `Idᵉ : Bᵉ → (Bᵉ → 𝒰)`.ᵉ

## Definitions

### The predicate of being a torsorial type family over `B`

```agda
is-torsorial-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Bᵉ : UUᵉ l1ᵉ} → (Bᵉ → UUᵉ l2ᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-torsorial-Propᵉ Eᵉ = is-contr-Propᵉ (Σᵉ _ Eᵉ)

is-prop-is-torsorialᵉ :
  {l1ᵉ l2ᵉ : Level} {Bᵉ : UUᵉ l1ᵉ} (Eᵉ : Bᵉ → UUᵉ l2ᵉ) → is-propᵉ (is-torsorialᵉ Eᵉ)
is-prop-is-torsorialᵉ Eᵉ = is-prop-type-Propᵉ (is-torsorial-Propᵉ Eᵉ)
```

### The type of torsorial type families over `B`

```agda
torsorial-family-of-typesᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
torsorial-family-of-typesᵉ l2ᵉ Bᵉ = Σᵉ (Bᵉ → UUᵉ l2ᵉ) is-torsorialᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Bᵉ : UUᵉ l1ᵉ} (Tᵉ : torsorial-family-of-typesᵉ l2ᵉ Bᵉ)
  where

  type-torsorial-family-of-typesᵉ : Bᵉ → UUᵉ l2ᵉ
  type-torsorial-family-of-typesᵉ = pr1ᵉ Tᵉ

  is-torsorial-torsorial-family-of-typesᵉ :
    is-torsorialᵉ type-torsorial-family-of-typesᵉ
  is-torsorial-torsorial-family-of-typesᵉ = pr2ᵉ Tᵉ
```

## Properties

### `fiber Id B ≃ is-torsorial B` for any type family `B` over `A`

Inᵉ otherᵉ words,ᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`ᵉ isᵉ in theᵉ
[image](foundation.images.mdᵉ) ofᵉ `Idᵉ : Aᵉ → (Aᵉ → 𝒰)`ᵉ ifᵉ andᵉ onlyᵉ ifᵉ `B`ᵉ isᵉ
torsorial.ᵉ Sinceᵉ beingᵉ contractibleᵉ isᵉ aᵉ
[proposition](foundation.propositions.md),ᵉ thisᵉ observationᵉ leadsᵉ to anᵉ
alternativeᵉ proofᵉ ofᵉ theᵉ aboveᵉ claimᵉ thatᵉ `Idᵉ : Aᵉ → (Aᵉ → 𝒰)`ᵉ isᵉ anᵉ
[embedding](foundation.embeddings.md).ᵉ Ourᵉ previousᵉ proofᵉ ofᵉ theᵉ factᵉ thatᵉ
`Idᵉ : Aᵉ → (Aᵉ → 𝒰)`ᵉ isᵉ anᵉ embeddingᵉ canᵉ beᵉ foundᵉ in
[`foundation.universal-property-identity-types`](foundation.universal-property-identity-types.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  is-torsorial-fiber-Idᵉ :
    {aᵉ : Aᵉ} → ((xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) ≃ᵉ Bᵉ xᵉ) → is-torsorialᵉ Bᵉ
  is-torsorial-fiber-Idᵉ Hᵉ =
    fundamental-theorem-id'ᵉ
      ( λ xᵉ → map-equivᵉ (Hᵉ xᵉ))
      ( λ xᵉ → is-equiv-map-equivᵉ (Hᵉ xᵉ))

  fiber-Id-is-torsorialᵉ :
    is-torsorialᵉ Bᵉ → Σᵉ Aᵉ (λ aᵉ → (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) ≃ᵉ Bᵉ xᵉ)
  pr1ᵉ (fiber-Id-is-torsorialᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ Hᵉ)) = aᵉ
  pr2ᵉ (fiber-Id-is-torsorialᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ Hᵉ)) =
    map-inv-distributive-Π-Σᵉ (fᵉ ,ᵉ fundamental-theorem-idᵉ ((aᵉ ,ᵉ bᵉ) ,ᵉ Hᵉ) fᵉ)
    where
    fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) → Bᵉ xᵉ
    fᵉ xᵉ reflᵉ = bᵉ

  compute-fiber-Idᵉ :
    (Σᵉ Aᵉ (λ aᵉ → (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) ≃ᵉ Bᵉ xᵉ)) ≃ᵉ is-torsorialᵉ Bᵉ
  compute-fiber-Idᵉ =
    equiv-iffᵉ
      ( Σᵉ Aᵉ (λ aᵉ → (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) ≃ᵉ Bᵉ xᵉ) ,ᵉ
        is-prop-total-family-of-equivalences-Idᵉ)
      ( is-contr-Propᵉ (Σᵉ Aᵉ Bᵉ))
      ( λ uᵉ → is-torsorial-fiber-Idᵉ (pr2ᵉ uᵉ))
      ( fiber-Id-is-torsorialᵉ)
```

### See also

-ᵉ [Discreteᵉ relations](foundation.discrete-relations.mdᵉ) areᵉ binaryᵉ torsorialᵉ
  typeᵉ families.ᵉ