# Dependent pair types

```agda
module foundation.dependent-pair-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`.ᵉ Theᵉ
{{#conceptᵉ "dependentᵉ pairᵉ type"ᵉ Agda=Σᵉ}} `Σᵉ Aᵉ B`ᵉ isᵉ theᵉ typeᵉ consistingᵉ ofᵉ
{{#conceptᵉ "(dependentᵉ) pairs"ᵉ Agda=pairᵉ Agda=_,ᵉ_}} `(aᵉ ,ᵉ b)`ᵉ where `aᵉ : A`ᵉ andᵉ
`bᵉ : Bᵉ a`.ᵉ Suchᵉ pairsᵉ areᵉ sometimesᵉ calledᵉ dependentᵉ pairsᵉ becauseᵉ theᵉ typeᵉ ofᵉ
`b`ᵉ dependsᵉ onᵉ theᵉ valueᵉ ofᵉ theᵉ firstᵉ componentᵉ `a`.ᵉ

## Definitions

### The dependent pair type

```agda
record Σᵉ {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ) where
  constructor pairᵉ
  field
    pr1ᵉ : Aᵉ
    pr2ᵉ : Bᵉ pr1ᵉ

open Σᵉ public


{-# INLINE pairᵉ #-}

infixr 3 _,ᵉ_
pattern _,ᵉ_ aᵉ bᵉ = pairᵉ aᵉ bᵉ
```

### The induction principle for dependent pair types

```agda
ind-Σᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Σᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ} →
  ((xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ (xᵉ ,ᵉ yᵉ)) → (tᵉ : Σᵉ Aᵉ Bᵉ) → Cᵉ tᵉ
ind-Σᵉ fᵉ (xᵉ ,ᵉ yᵉ) = fᵉ xᵉ yᵉ
```

### The recursion principle for dependent pair types

```agda
rec-Σᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} →
  ((xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ) → Σᵉ Aᵉ Bᵉ → Cᵉ
rec-Σᵉ = ind-Σᵉ
```

### The evaluation function for dependent pairs

```agda
ev-pairᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Σᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ} →
  ((tᵉ : Σᵉ Aᵉ Bᵉ) → Cᵉ tᵉ) → (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ (xᵉ ,ᵉ yᵉ)
ev-pairᵉ fᵉ xᵉ yᵉ = fᵉ (xᵉ ,ᵉ yᵉ)
```

Weᵉ showᵉ thatᵉ `ev-pair`ᵉ isᵉ theᵉ inverseᵉ to `ind-Σ`ᵉ in
[`foundation.universal-property-dependent-pair-types`](foundation.universal-property-dependent-pair-types.md).ᵉ

### Iterated dependent pair constructors

```agda
tripleᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ} →
  (aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ) → Cᵉ aᵉ bᵉ → Σᵉ Aᵉ (λ xᵉ → Σᵉ (Bᵉ xᵉ) (Cᵉ xᵉ))
tripleᵉ aᵉ bᵉ cᵉ = (aᵉ ,ᵉ bᵉ ,ᵉ cᵉ)

triple'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Σᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ} →
  (aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ) → Cᵉ (pairᵉ aᵉ bᵉ) → Σᵉ (Σᵉ Aᵉ Bᵉ) Cᵉ
triple'ᵉ aᵉ bᵉ cᵉ = ((aᵉ ,ᵉ bᵉ) ,ᵉ cᵉ)
```

### Families on dependent pair types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  fam-Σᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ) → Σᵉ Aᵉ Bᵉ → UUᵉ l3ᵉ
  fam-Σᵉ Cᵉ (xᵉ ,ᵉ yᵉ) = Cᵉ xᵉ yᵉ
```