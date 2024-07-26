# Quotients of finite types

```agda
module univalent-combinatorics.quotients-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.decidable-equivalence-relationsᵉ
open import univalent-combinatorics.decidable-subtypesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.image-of-mapsᵉ
```

</details>

## Idea

Theᵉ quotientᵉ ofᵉ aᵉ finiteᵉ typeᵉ byᵉ aᵉ decidableᵉ equivalenceᵉ relationᵉ isᵉ againᵉ aᵉ
finiteᵉ type.ᵉ Inᵉ thisᵉ fileᵉ weᵉ setᵉ upᵉ someᵉ infrastructureᵉ forᵉ suchᵉ quotients.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Rᵉ : Decidable-equivalence-relation-𝔽ᵉ l2ᵉ Xᵉ)
  where

  equivalence-class-Decidable-equivalence-relation-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  equivalence-class-Decidable-equivalence-relation-𝔽ᵉ =
    imᵉ (decidable-relation-Decidable-equivalence-relation-𝔽ᵉ Xᵉ Rᵉ)

  is-finite-equivalence-class-Decidable-equivalence-relation-𝔽'ᵉ :
    is-finiteᵉ equivalence-class-Decidable-equivalence-relation-𝔽ᵉ
  is-finite-equivalence-class-Decidable-equivalence-relation-𝔽'ᵉ =
    is-finite-imᵉ
      ( is-finite-type-𝔽ᵉ Xᵉ)
      ( has-decidable-equality-Subset-𝔽ᵉ Xᵉ)

  quotient-𝔽ᵉ : 𝔽ᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  pr1ᵉ quotient-𝔽ᵉ = equivalence-class-Decidable-equivalence-relation-𝔽ᵉ
  pr2ᵉ quotient-𝔽ᵉ = is-finite-equivalence-class-Decidable-equivalence-relation-𝔽'ᵉ
```