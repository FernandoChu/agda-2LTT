# Standard apartness relations

```agda
module foundation.standard-apartness-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relationsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.law-of-excluded-middleᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.tight-apartness-relationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
open import foundation-core.negationᵉ
```

</details>

## Idea

Anᵉ [apartnessᵉ relation](foundation.apartness-relations.mdᵉ) `#`ᵉ isᵉ saidᵉ to beᵉ
**standard**ᵉ ifᵉ theᵉ
[lawᵉ ofᵉ excludedᵉ middle](foundation.law-of-excluded-middle.mdᵉ) impliesᵉ thatᵉ `#`ᵉ
isᵉ [equivalent](foundation.logical-equivalences.mdᵉ) to
[negatedᵉ equality](foundation.negated-equality.md).ᵉ

## Definition

```agda
is-standard-Apartness-Relationᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Apartness-Relationᵉ l2ᵉ Aᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
is-standard-Apartness-Relationᵉ {l1ᵉ} {l2ᵉ} l3ᵉ {Aᵉ} Rᵉ =
  LEMᵉ l3ᵉ → (xᵉ yᵉ : Aᵉ) → (xᵉ ≠ᵉ yᵉ) ↔ᵉ apart-Apartness-Relationᵉ Rᵉ xᵉ yᵉ
```

## Properties

### Any tight apartness relation is standard

```agda
is-standard-is-tight-Apartness-Relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Apartness-Relationᵉ l2ᵉ Aᵉ) →
  is-tight-Apartness-Relationᵉ Rᵉ → is-standard-Apartness-Relationᵉ l2ᵉ Rᵉ
pr1ᵉ (is-standard-is-tight-Apartness-Relationᵉ Rᵉ Hᵉ lemᵉ xᵉ yᵉ) npᵉ =
  double-negation-elim-is-decidableᵉ
    ( lemᵉ (rel-Apartness-Relationᵉ Rᵉ xᵉ yᵉ))
    ( map-negᵉ (Hᵉ xᵉ yᵉ) npᵉ)
pr2ᵉ (is-standard-is-tight-Apartness-Relationᵉ Rᵉ Hᵉ lemᵉ xᵉ .xᵉ) rᵉ reflᵉ =
  antirefl-Apartness-Relationᵉ Rᵉ xᵉ rᵉ
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ MRR88ᵉ}}