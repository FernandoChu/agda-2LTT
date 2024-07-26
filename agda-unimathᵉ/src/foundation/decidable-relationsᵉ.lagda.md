# Decidable relations on types

```agda
module foundation.decidable-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.decidable-propositionsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ **decidableᵉ (binaryᵉ) relation**ᵉ onᵉ `X`ᵉ isᵉ aᵉ binaryᵉ relationᵉ `R`ᵉ onᵉ `X`ᵉ suchᵉ
thatᵉ eachᵉ `Rᵉ xᵉ y`ᵉ isᵉ aᵉ decidableᵉ proposition.ᵉ

## Definitions

### Decidable relations

```agda
is-decidable-Relation-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → Relation-Propᵉ l2ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-decidable-Relation-Propᵉ {Aᵉ = Aᵉ} Rᵉ =
  (xᵉ yᵉ : Aᵉ) → is-decidableᵉ ( type-Relation-Propᵉ Rᵉ xᵉ yᵉ)

Decidable-Relationᵉ : {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Decidable-Relationᵉ l2ᵉ Xᵉ = Xᵉ → Xᵉ → Decidable-Propᵉ l2ᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Rᵉ : Decidable-Relationᵉ l2ᵉ Xᵉ)
  where

  relation-Decidable-Relationᵉ : Xᵉ → Xᵉ → Propᵉ l2ᵉ
  relation-Decidable-Relationᵉ xᵉ yᵉ = prop-Decidable-Propᵉ (Rᵉ xᵉ yᵉ)

  rel-Decidable-Relationᵉ : Xᵉ → Xᵉ → UUᵉ l2ᵉ
  rel-Decidable-Relationᵉ xᵉ yᵉ = type-Decidable-Propᵉ (Rᵉ xᵉ yᵉ)

  is-prop-rel-Decidable-Relationᵉ :
    (xᵉ yᵉ : Xᵉ) → is-propᵉ (rel-Decidable-Relationᵉ xᵉ yᵉ)
  is-prop-rel-Decidable-Relationᵉ xᵉ yᵉ = is-prop-type-Decidable-Propᵉ (Rᵉ xᵉ yᵉ)

  is-decidable-Decidable-Relationᵉ :
    (xᵉ yᵉ : Xᵉ) → is-decidableᵉ (rel-Decidable-Relationᵉ xᵉ yᵉ)
  is-decidable-Decidable-Relationᵉ xᵉ yᵉ =
    is-decidable-Decidable-Propᵉ (Rᵉ xᵉ yᵉ)

map-inv-equiv-relation-is-decidable-Decidable-Relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} →
  Σᵉ ( Relation-Propᵉ l2ᵉ Xᵉ) (λ Rᵉ → is-decidable-Relation-Propᵉ Rᵉ) →
  Decidable-Relationᵉ l2ᵉ Xᵉ
map-inv-equiv-relation-is-decidable-Decidable-Relationᵉ (Rᵉ ,ᵉ dᵉ) xᵉ yᵉ =
  ( ( type-Relation-Propᵉ Rᵉ xᵉ yᵉ) ,ᵉ
    ( is-prop-type-Relation-Propᵉ Rᵉ xᵉ yᵉ) ,ᵉ
    ( dᵉ xᵉ yᵉ))

equiv-relation-is-decidable-Decidable-Relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} →
  Decidable-Relationᵉ l2ᵉ Xᵉ ≃ᵉ
  Σᵉ ( Relation-Propᵉ l2ᵉ Xᵉ) (λ Rᵉ → is-decidable-Relation-Propᵉ Rᵉ)
pr1ᵉ equiv-relation-is-decidable-Decidable-Relationᵉ dec-Rᵉ =
  ( relation-Decidable-Relationᵉ dec-Rᵉ ,ᵉ
    is-decidable-Decidable-Relationᵉ dec-Rᵉ)
pr2ᵉ equiv-relation-is-decidable-Decidable-Relationᵉ =
  is-equiv-is-invertibleᵉ
    ( map-inv-equiv-relation-is-decidable-Decidable-Relationᵉ)
    ( refl-htpyᵉ)
    ( refl-htpyᵉ)
```