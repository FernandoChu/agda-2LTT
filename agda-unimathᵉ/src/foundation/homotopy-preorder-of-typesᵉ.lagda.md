# The homotopy preorder of types

```agda
module
  foundation.homotopy-preorder-of-typesᵉ
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-functionsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-preordersᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "homotopyᵉ preorderᵉ ofᵉ types"ᵉ Agda=Homotopy-Type-Large-Preorderᵉ}}
isᵉ theᵉ [(largeᵉ) preorder](order-theory.large-preorders.mdᵉ) whoseᵉ objectsᵉ areᵉ
types,ᵉ andᵉ whoseᵉ orderingᵉ relationᵉ isᵉ definedᵉ byᵉ
[mereᵉ functions](foundation.mere-functions.md),ᵉ i.e.ᵉ byᵉ theᵉ
[propositionalᵉ truncation](foundation.propositional-truncations.mdᵉ) ofᵉ theᵉ
functionᵉ typesᵉ:

```text
  Aᵉ ≤ᵉ Bᵉ :=ᵉ ║(Aᵉ → B)║₋₁.ᵉ
```

## Definitions

### The large homotopy preorder of types

```agda
Homotopy-Type-Large-Preorderᵉ : Large-Preorderᵉ lsuc (_⊔ᵉ_)
Homotopy-Type-Large-Preorderᵉ =
  λ where
  .type-Large-Preorderᵉ lᵉ → UUᵉ lᵉ
  .leq-prop-Large-Preorderᵉ → prop-mere-functionᵉ
  .refl-leq-Large-Preorderᵉ → refl-mere-functionᵉ
  .transitive-leq-Large-Preorderᵉ Xᵉ Yᵉ Zᵉ → transitive-mere-functionᵉ
```

### The small homotopy preorder of types

```agda
Homotopy-Type-Preorderᵉ : (lᵉ : Level) → Preorderᵉ (lsuc lᵉ) lᵉ
Homotopy-Type-Preorderᵉ = preorder-Large-Preorderᵉ Homotopy-Type-Large-Preorderᵉ
```