# Large subpreorders

```agda
module order-theory.large-subpreordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-preordersᵉ
```

</details>

## Idea

Aᵉ **largeᵉ subpreorder**ᵉ ofᵉ aᵉ [largeᵉ preorder](order-theory.large-preorders.mdᵉ)
`P`ᵉ consistsᵉ ofᵉ aᵉ subtypeᵉ

```text
  Sᵉ : type-Large-Preorderᵉ Pᵉ lᵉ → Propᵉ (γᵉ lᵉ)
```

forᵉ eachᵉ universeᵉ levelᵉ `l`,ᵉ where `γᵉ : Level → Level`ᵉ isᵉ aᵉ universeᵉ levelᵉ
reindexingᵉ function.ᵉ

## Definition

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (γᵉ : Level → Level)
  (Pᵉ : Large-Preorderᵉ αᵉ βᵉ)
  where

  Large-Subpreorderᵉ : UUωᵉ
  Large-Subpreorderᵉ = {lᵉ : Level} → type-Large-Preorderᵉ Pᵉ lᵉ → Propᵉ (γᵉ lᵉ)

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Pᵉ : Large-Preorderᵉ αᵉ βᵉ) (Sᵉ : Large-Subpreorderᵉ γᵉ Pᵉ)
  where

  is-in-Large-Subpreorderᵉ :
    {l1ᵉ : Level} → type-Large-Preorderᵉ Pᵉ l1ᵉ → UUᵉ (γᵉ l1ᵉ)
  is-in-Large-Subpreorderᵉ {l1ᵉ} = is-in-subtypeᵉ (Sᵉ {l1ᵉ})

  is-prop-is-in-Large-Subpreorderᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Preorderᵉ Pᵉ l1ᵉ) →
    is-propᵉ (is-in-Large-Subpreorderᵉ xᵉ)
  is-prop-is-in-Large-Subpreorderᵉ {l1ᵉ} =
    is-prop-is-in-subtypeᵉ (Sᵉ {l1ᵉ})

  type-Large-Subpreorderᵉ : (l1ᵉ : Level) → UUᵉ (αᵉ l1ᵉ ⊔ γᵉ l1ᵉ)
  type-Large-Subpreorderᵉ l1ᵉ = type-subtypeᵉ (Sᵉ {l1ᵉ})

  leq-prop-Large-Subpreorderᵉ :
    Large-Relation-Propᵉ βᵉ type-Large-Subpreorderᵉ
  leq-prop-Large-Subpreorderᵉ xᵉ yᵉ =
    leq-prop-Large-Preorderᵉ Pᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ)

  leq-Large-Subpreorderᵉ :
    Large-Relationᵉ βᵉ type-Large-Subpreorderᵉ
  leq-Large-Subpreorderᵉ xᵉ yᵉ = type-Propᵉ (leq-prop-Large-Subpreorderᵉ xᵉ yᵉ)

  is-prop-leq-Large-Subpreorderᵉ :
    is-prop-Large-Relationᵉ type-Large-Subpreorderᵉ leq-Large-Subpreorderᵉ
  is-prop-leq-Large-Subpreorderᵉ xᵉ yᵉ =
    is-prop-type-Propᵉ (leq-prop-Large-Subpreorderᵉ xᵉ yᵉ)

  refl-leq-Large-Subpreorderᵉ :
    is-reflexive-Large-Relationᵉ type-Large-Subpreorderᵉ leq-Large-Subpreorderᵉ
  refl-leq-Large-Subpreorderᵉ (xᵉ ,ᵉ pᵉ) = refl-leq-Large-Preorderᵉ Pᵉ xᵉ

  transitive-leq-Large-Subpreorderᵉ :
    is-transitive-Large-Relationᵉ type-Large-Subpreorderᵉ leq-Large-Subpreorderᵉ
  transitive-leq-Large-Subpreorderᵉ (xᵉ ,ᵉ pᵉ) (yᵉ ,ᵉ qᵉ) (zᵉ ,ᵉ rᵉ) =
    transitive-leq-Large-Preorderᵉ Pᵉ xᵉ yᵉ zᵉ

  large-preorder-Large-Subpreorderᵉ :
    Large-Preorderᵉ (λ lᵉ → αᵉ lᵉ ⊔ γᵉ lᵉ) (λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ)
  type-Large-Preorderᵉ
    large-preorder-Large-Subpreorderᵉ =
    type-Large-Subpreorderᵉ
  leq-prop-Large-Preorderᵉ
    large-preorder-Large-Subpreorderᵉ =
    leq-prop-Large-Subpreorderᵉ
  refl-leq-Large-Preorderᵉ
    large-preorder-Large-Subpreorderᵉ =
    refl-leq-Large-Subpreorderᵉ
  transitive-leq-Large-Preorderᵉ
    large-preorder-Large-Subpreorderᵉ =
    transitive-leq-Large-Subpreorderᵉ
```