# Reflexive relations

```agda
module foundation.reflexive-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "reflexiveᵉ relation"ᵉ Agda=Reflexive-Relationᵉ}} onᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ
type-valuedᵉ [binaryᵉ relation](foundation.binary-relations.mdᵉ) `Rᵉ : Aᵉ → Aᵉ → 𝒰`ᵉ
[equipped](foundation.structure.mdᵉ) with aᵉ proofᵉ `rᵉ : (xᵉ : Aᵉ) → Rᵉ xᵉ x`.ᵉ

## Definitions

### Reflexive relations

```agda
Reflexive-Relationᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Reflexive-Relationᵉ l2ᵉ Aᵉ = Σᵉ (Relationᵉ l2ᵉ Aᵉ) (λ Rᵉ → is-reflexiveᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Reflexive-Relationᵉ l2ᵉ Aᵉ)
  where

  rel-Reflexive-Relationᵉ : Relationᵉ l2ᵉ Aᵉ
  rel-Reflexive-Relationᵉ = pr1ᵉ Rᵉ

  is-reflexive-Reflexive-Relationᵉ : is-reflexiveᵉ rel-Reflexive-Relationᵉ
  is-reflexive-Reflexive-Relationᵉ = pr2ᵉ Rᵉ
```

### The identity reflexive relation on a type

```agda
Id-Reflexive-Relationᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → Reflexive-Relationᵉ lᵉ Aᵉ
Id-Reflexive-Relationᵉ Aᵉ = (Idᵉ ,ᵉ (λ xᵉ → reflᵉ))
```