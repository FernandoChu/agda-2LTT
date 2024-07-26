# Coproduct types

```agda
module foundation-core.coproduct-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "coproduct"ᵉ Disambiguation="ofᵉ types"ᵉ}} ofᵉ twoᵉ typesᵉ `A`ᵉ andᵉ `B`ᵉ
canᵉ beᵉ thoughtᵉ ofᵉ asᵉ theᵉ disjointᵉ unionᵉ ofᵉ `A`ᵉ andᵉ `B`.ᵉ

## Definition

### Coproduct types

```agda
infixr 10 _+ᵉ_

data _+ᵉ_ {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  where
  inlᵉ : Aᵉ → Aᵉ +ᵉ Bᵉ
  inrᵉ : Bᵉ → Aᵉ +ᵉ Bᵉ
```

### The induction principle for coproduct types

```agda
ind-coproductᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Cᵉ : Aᵉ +ᵉ Bᵉ → UUᵉ l3ᵉ) →
  ((xᵉ : Aᵉ) → Cᵉ (inlᵉ xᵉ)) → ((yᵉ : Bᵉ) → Cᵉ (inrᵉ yᵉ)) →
  (tᵉ : Aᵉ +ᵉ Bᵉ) → Cᵉ tᵉ
ind-coproductᵉ Cᵉ fᵉ gᵉ (inlᵉ xᵉ) = fᵉ xᵉ
ind-coproductᵉ Cᵉ fᵉ gᵉ (inrᵉ xᵉ) = gᵉ xᵉ
```

### The recursion principle for coproduct types

```agda
rec-coproductᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} →
  (Aᵉ → Cᵉ) → (Bᵉ → Cᵉ) → (Aᵉ +ᵉ Bᵉ) → Cᵉ
rec-coproductᵉ {Cᵉ = Cᵉ} = ind-coproductᵉ (λ _ → Cᵉ)
```