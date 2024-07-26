# Discrete relations

```agda
module foundation.discrete-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.reflexive-relationsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ [relation](foundation.binary-relations.mdᵉ) `R`ᵉ onᵉ `A`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "discrete"ᵉ Disambiguation="binaryᵉ relationsᵉ valuedᵉ in types"ᵉ Agda=is-discrete-Relationᵉ}}
if,ᵉ forᵉ everyᵉ elementᵉ `xᵉ : A`,ᵉ theᵉ typeᵉ familyᵉ `Rᵉ x`ᵉ isᵉ
[torsorial](foundation-core.torsorial-type-families.md).ᵉ Inᵉ otherᵉ words,ᵉ theᵉ
[dependentᵉ sum](foundation.dependent-pair-types.mdᵉ) `Σᵉ (yᵉ : A),ᵉ (Rᵉ xᵉ y)`ᵉ isᵉ
[contractible](foundation-core.contractible-types.mdᵉ) forᵉ everyᵉ `x`.ᵉ Theᵉ
{{#conceptᵉ "standardᵉ discreteᵉ relation"ᵉ Disambiguation="binaryᵉ relationsᵉ valuedᵉ in types"ᵉ}}
onᵉ aᵉ typeᵉ `X`ᵉ isᵉ theᵉ relationᵉ definedᵉ byᵉ
[identifications](foundation-core.identity-types.md),ᵉ

```text
  Rᵉ xᵉ yᵉ :=ᵉ (xᵉ ＝ᵉ y).ᵉ
```

## Definitions

### The predicate on relations of being discrete

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  is-discrete-prop-Relationᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-discrete-prop-Relationᵉ = Π-Propᵉ Aᵉ (λ xᵉ → is-torsorial-Propᵉ (Rᵉ xᵉ))

  is-discrete-Relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-discrete-Relationᵉ =
    type-Propᵉ is-discrete-prop-Relationᵉ

  is-prop-is-discrete-Relationᵉ : is-propᵉ is-discrete-Relationᵉ
  is-prop-is-discrete-Relationᵉ =
    is-prop-type-Propᵉ is-discrete-prop-Relationᵉ
```

### The predicate on reflexive relations of being discrete

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Reflexive-Relationᵉ l2ᵉ Aᵉ)
  where

  is-discrete-prop-Reflexive-Relationᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-discrete-prop-Reflexive-Relationᵉ =
    is-discrete-prop-Relationᵉ (rel-Reflexive-Relationᵉ Rᵉ)

  is-discrete-Reflexive-Relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-discrete-Reflexive-Relationᵉ =
    type-Propᵉ is-discrete-prop-Reflexive-Relationᵉ

  is-prop-is-discrete-Reflexive-Relationᵉ :
    is-propᵉ is-discrete-Reflexive-Relationᵉ
  is-prop-is-discrete-Reflexive-Relationᵉ =
    is-prop-type-Propᵉ is-discrete-prop-Reflexive-Relationᵉ
```

### The standard discrete relation on a type

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  is-discrete-Id-Relationᵉ : is-discrete-Relationᵉ (Idᵉ {Aᵉ = Aᵉ})
  is-discrete-Id-Relationᵉ = is-torsorial-Idᵉ
```