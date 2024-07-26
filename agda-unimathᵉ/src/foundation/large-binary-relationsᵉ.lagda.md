# Large binary relations

```agda
module foundation.large-binary-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "largeᵉ binaryᵉ relation"ᵉ Disambiguation="valuedᵉ in types"ᵉ Agda=Large-Relationᵉ}}
onᵉ aᵉ familyᵉ ofᵉ typesᵉ indexedᵉ byᵉ universeᵉ levelsᵉ `A`ᵉ isᵉ aᵉ familyᵉ ofᵉ typesᵉ `Rᵉ xᵉ y`ᵉ
dependingᵉ onᵉ twoᵉ variablesᵉ `xᵉ : Aᵉ l1`ᵉ andᵉ `yᵉ : Aᵉ l2`.ᵉ Inᵉ theᵉ specialᵉ caseᵉ where
eachᵉ `Rᵉ xᵉ y`ᵉ isᵉ aᵉ [proposition](foundation-core.propositions.md),ᵉ weᵉ sayᵉ thatᵉ
theᵉ relationᵉ isᵉ valuedᵉ in propositions.ᵉ Thus,ᵉ weᵉ takeᵉ aᵉ generalᵉ relationᵉ to meanᵉ
aᵉ _proof-relevantᵉ_ relation.ᵉ

## Definition

### Large relations valued in types

```agda
module _
  {αᵉ : Level → Level} (βᵉ : Level → Level → Level)
  (Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ))
  where

  Large-Relationᵉ : UUωᵉ
  Large-Relationᵉ = {l1ᵉ l2ᵉ : Level} → Aᵉ l1ᵉ → Aᵉ l2ᵉ → UUᵉ (βᵉ l1ᵉ l2ᵉ)

  total-space-Large-Relationᵉ : Large-Relationᵉ → UUωᵉ
  total-space-Large-Relationᵉ Rᵉ =
    (l1ᵉ l2ᵉ : Level) → Σᵉ (Aᵉ l1ᵉ ×ᵉ Aᵉ l2ᵉ) (λ (aᵉ ,ᵉ a'ᵉ) → Rᵉ aᵉ a'ᵉ)
```

### Large relations valued in propositions

```agda
is-prop-Large-Relationᵉ :
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)) → Large-Relationᵉ βᵉ Aᵉ → UUωᵉ
is-prop-Large-Relationᵉ Aᵉ Rᵉ =
  {l1ᵉ l2ᵉ : Level} (xᵉ : Aᵉ l1ᵉ) (yᵉ : Aᵉ l2ᵉ) → is-propᵉ (Rᵉ xᵉ yᵉ)

Large-Relation-Propᵉ :
  {αᵉ : Level → Level} (βᵉ : Level → Level → Level)
  (Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)) →
  UUωᵉ
Large-Relation-Propᵉ βᵉ Aᵉ = {l1ᵉ l2ᵉ : Level} → Aᵉ l1ᵉ → Aᵉ l2ᵉ → Propᵉ (βᵉ l1ᵉ l2ᵉ)

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ))
  (Rᵉ : Large-Relation-Propᵉ βᵉ Aᵉ)
  where

  large-relation-Large-Relation-Propᵉ : Large-Relationᵉ βᵉ Aᵉ
  large-relation-Large-Relation-Propᵉ xᵉ yᵉ = type-Propᵉ (Rᵉ xᵉ yᵉ)

  is-prop-large-relation-Large-Relation-Propᵉ :
    is-prop-Large-Relationᵉ Aᵉ large-relation-Large-Relation-Propᵉ
  is-prop-large-relation-Large-Relation-Propᵉ xᵉ yᵉ = is-prop-type-Propᵉ (Rᵉ xᵉ yᵉ)

  total-space-Large-Relation-Propᵉ : UUωᵉ
  total-space-Large-Relation-Propᵉ =
    (l1ᵉ l2ᵉ : Level) →
    Σᵉ (Aᵉ l1ᵉ ×ᵉ Aᵉ l2ᵉ) (λ (aᵉ ,ᵉ a'ᵉ) → large-relation-Large-Relation-Propᵉ aᵉ a'ᵉ)
```

## Small relations from large relations

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ))
  where

  relation-Large-Relationᵉ :
    (Rᵉ : Large-Relationᵉ βᵉ Aᵉ) (lᵉ : Level) → Relationᵉ (βᵉ lᵉ lᵉ) (Aᵉ lᵉ)
  relation-Large-Relationᵉ Rᵉ lᵉ xᵉ yᵉ = Rᵉ xᵉ yᵉ

  relation-prop-Large-Relation-Propᵉ :
    (Rᵉ : Large-Relation-Propᵉ βᵉ Aᵉ) (lᵉ : Level) → Relation-Propᵉ (βᵉ lᵉ lᵉ) (Aᵉ lᵉ)
  relation-prop-Large-Relation-Propᵉ Rᵉ lᵉ xᵉ yᵉ = Rᵉ xᵉ yᵉ

  relation-Large-Relation-Propᵉ :
    (Rᵉ : Large-Relation-Propᵉ βᵉ Aᵉ) (lᵉ : Level) → Relationᵉ (βᵉ lᵉ lᵉ) (Aᵉ lᵉ)
  relation-Large-Relation-Propᵉ Rᵉ =
    relation-Large-Relationᵉ (large-relation-Large-Relation-Propᵉ Aᵉ Rᵉ)
```

## Specifications of properties of binary relations

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ))
  (Rᵉ : Large-Relationᵉ βᵉ Aᵉ)
  where

  is-reflexive-Large-Relationᵉ : UUωᵉ
  is-reflexive-Large-Relationᵉ = {lᵉ : Level} (xᵉ : Aᵉ lᵉ) → Rᵉ xᵉ xᵉ

  is-symmetric-Large-Relationᵉ : UUωᵉ
  is-symmetric-Large-Relationᵉ =
    {l1ᵉ l2ᵉ : Level} (xᵉ : Aᵉ l1ᵉ) (yᵉ : Aᵉ l2ᵉ) → Rᵉ xᵉ yᵉ → Rᵉ yᵉ xᵉ

  is-transitive-Large-Relationᵉ : UUωᵉ
  is-transitive-Large-Relationᵉ =
    {l1ᵉ l2ᵉ l3ᵉ : Level} (xᵉ : Aᵉ l1ᵉ) (yᵉ : Aᵉ l2ᵉ) (zᵉ : Aᵉ l3ᵉ) → Rᵉ yᵉ zᵉ → Rᵉ xᵉ yᵉ → Rᵉ xᵉ zᵉ

  is-antisymmetric-Large-Relationᵉ : UUωᵉ
  is-antisymmetric-Large-Relationᵉ =
    {lᵉ : Level} → is-antisymmetricᵉ (relation-Large-Relationᵉ Aᵉ Rᵉ lᵉ)

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Aᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ))
  (Rᵉ : Large-Relation-Propᵉ βᵉ Aᵉ)
  where

  is-reflexive-Large-Relation-Propᵉ : UUωᵉ
  is-reflexive-Large-Relation-Propᵉ =
    is-reflexive-Large-Relationᵉ Aᵉ (large-relation-Large-Relation-Propᵉ Aᵉ Rᵉ)

  is-symmetric-Large-Relation-Propᵉ : UUωᵉ
  is-symmetric-Large-Relation-Propᵉ =
    is-symmetric-Large-Relationᵉ Aᵉ (large-relation-Large-Relation-Propᵉ Aᵉ Rᵉ)

  is-transitive-Large-Relation-Propᵉ : UUωᵉ
  is-transitive-Large-Relation-Propᵉ =
    is-transitive-Large-Relationᵉ Aᵉ (large-relation-Large-Relation-Propᵉ Aᵉ Rᵉ)

  is-antisymmetric-Large-Relation-Propᵉ : UUωᵉ
  is-antisymmetric-Large-Relation-Propᵉ =
    is-antisymmetric-Large-Relationᵉ Aᵉ (large-relation-Large-Relation-Propᵉ Aᵉ Rᵉ)
```

## See also

-ᵉ [(Smallᵉ) binaryᵉ relations](foundation.binary-relations.mdᵉ)
-ᵉ [Largeᵉ preorders](order-theory.large-preorders.mdᵉ)
-ᵉ [Largeᵉ posets](order-theory.large-posets.mdᵉ)