# Discrete graphs

```agda
module graph-theory.discrete-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.discrete-relationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.reflexive-graphsᵉ
```

</details>

## Idea

Aᵉ [directedᵉ graph](graph-theory.directed-graphs.mdᵉ) `Gᵉ ≐ᵉ (Vᵉ ,ᵉ E)`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "discrete"ᵉ Disambiguation="graph"ᵉ Agda=is-discrete-Graphᵉ}} if,ᵉ forᵉ
everyᵉ vertexᵉ `xᵉ : V`,ᵉ theᵉ typeᵉ familyᵉ ofᵉ edgesᵉ with sourceᵉ `x`,ᵉ `Eᵉ x`,ᵉ isᵉ
[torsorial](foundation-core.torsorial-type-families.md).ᵉ Inᵉ otherᵉ words,ᵉ ifᵉ theᵉ
[dependentᵉ sum](foundation.dependent-pair-types.mdᵉ) `Σᵉ (yᵉ : V),ᵉ (Eᵉ xᵉ y)`ᵉ isᵉ
[contractible](foundation-core.contractible-types.mdᵉ) forᵉ everyᵉ `x`.ᵉ Theᵉ
{{#conceptᵉ "standardᵉ discreteᵉ graph"ᵉ}} associatedᵉ to aᵉ typeᵉ `X`ᵉ isᵉ theᵉ graphᵉ
whoseᵉ verticesᵉ areᵉ elementsᵉ ofᵉ `X`,ᵉ andᵉ edgesᵉ areᵉ
[identifications](foundation-core.identity-types.md),ᵉ

```text
  Eᵉ xᵉ yᵉ :=ᵉ (xᵉ ＝ᵉ y).ᵉ
```

## Definitions

### The predicate on graphs of being discrete

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  is-discrete-prop-Graphᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-discrete-prop-Graphᵉ = is-discrete-prop-Relationᵉ (edge-Directed-Graphᵉ Gᵉ)

  is-discrete-Graphᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-discrete-Graphᵉ = type-Propᵉ is-discrete-prop-Graphᵉ

  is-prop-is-discrete-Graphᵉ : is-propᵉ is-discrete-Graphᵉ
  is-prop-is-discrete-Graphᵉ = is-prop-type-Propᵉ is-discrete-prop-Graphᵉ
```

### The predicate on reflexive graphs of being discrete

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Reflexive-Graphᵉ l1ᵉ l2ᵉ)
  where

  is-discrete-prop-Reflexive-Graphᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-discrete-prop-Reflexive-Graphᵉ =
    is-discrete-prop-Graphᵉ (graph-Reflexive-Graphᵉ Gᵉ)

  is-discrete-Reflexive-Graphᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-discrete-Reflexive-Graphᵉ =
    type-Propᵉ is-discrete-prop-Reflexive-Graphᵉ

  is-prop-is-discrete-Reflexive-Graphᵉ : is-propᵉ is-discrete-Reflexive-Graphᵉ
  is-prop-is-discrete-Reflexive-Graphᵉ =
    is-prop-type-Propᵉ is-discrete-prop-Reflexive-Graphᵉ
```