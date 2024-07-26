# The interchange law

```agda
module foundation.interchange-lawᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Theᵉ interchangeᵉ lawᵉ showsᵉ upᵉ in manyᵉ variationsᵉ in typeᵉ theory.ᵉ Theᵉ interchangeᵉ
lawᵉ forᵉ Σ-typesᵉ isᵉ usefulᵉ in characterizationsᵉ ofᵉ identityᵉ types;ᵉ theᵉ
interchangeᵉ lawᵉ forᵉ higherᵉ identityᵉ typesᵉ isᵉ usedᵉ in theᵉ Eckmann-Hiltonᵉ argumentᵉ
to showᵉ thatᵉ theᵉ higherᵉ homotopyᵉ groupsᵉ ofᵉ aᵉ typeᵉ areᵉ abelian,ᵉ andᵉ theᵉ
interchangeᵉ lawᵉ forᵉ binaryᵉ operationsᵉ in ringsᵉ areᵉ usefulᵉ in computations.ᵉ Weᵉ
firstᵉ defineᵉ aᵉ fullyᵉ generalizedᵉ interchangeᵉ law,ᵉ andᵉ thenᵉ weᵉ specializeᵉ itᵉ to
makeᵉ itᵉ moreᵉ directlyᵉ applicable.ᵉ

## Definition

### The fully generalized interchange law

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ l10ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ} {Dᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ → Cᵉ aᵉ → UUᵉ l4ᵉ}
  {X1ᵉ : UUᵉ l5ᵉ} {Y1ᵉ : X1ᵉ → UUᵉ l6ᵉ} {X2ᵉ : UUᵉ l7ᵉ} {Y2ᵉ : X2ᵉ → UUᵉ l8ᵉ}
  {Zᵉ : UUᵉ l9ᵉ} (Rᵉ : Zᵉ → Zᵉ → UUᵉ l10ᵉ)
  (μ1ᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ → X1ᵉ)
  (μ2ᵉ : (aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ) (cᵉ : Cᵉ aᵉ) → Dᵉ aᵉ bᵉ cᵉ → Y1ᵉ (μ1ᵉ aᵉ bᵉ))
  (μ3ᵉ : (xᵉ : X1ᵉ) → Y1ᵉ xᵉ → Zᵉ)
  (μ4ᵉ : (aᵉ : Aᵉ) → Cᵉ aᵉ → X2ᵉ)
  (μ5ᵉ : (aᵉ : Aᵉ) (cᵉ : Cᵉ aᵉ) (bᵉ : Bᵉ aᵉ) → Dᵉ aᵉ bᵉ cᵉ → Y2ᵉ (μ4ᵉ aᵉ cᵉ))
  (μ6ᵉ : (xᵉ : X2ᵉ) → Y2ᵉ xᵉ → Zᵉ)
  where

  fully-generalized-interchange-lawᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l10ᵉ)
  fully-generalized-interchange-lawᵉ =
    (aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ) (cᵉ : Cᵉ aᵉ) (dᵉ : Dᵉ aᵉ bᵉ cᵉ) →
    Rᵉ (μ3ᵉ (μ1ᵉ aᵉ bᵉ) (μ2ᵉ aᵉ bᵉ cᵉ dᵉ)) (μ6ᵉ (μ4ᵉ aᵉ cᵉ) (μ5ᵉ aᵉ cᵉ bᵉ dᵉ))
```

### The interchange law for two binary operations on a type

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (μᵉ : Xᵉ → Xᵉ → Xᵉ)
  where

  interchange-lawᵉ : (Xᵉ → Xᵉ → Xᵉ) → UUᵉ lᵉ
  interchange-lawᵉ νᵉ = (xᵉ yᵉ uᵉ vᵉ : Xᵉ) → μᵉ (νᵉ xᵉ yᵉ) (νᵉ uᵉ vᵉ) ＝ᵉ νᵉ (μᵉ xᵉ uᵉ) (μᵉ yᵉ vᵉ)

  interchange-law-commutative-and-associativeᵉ :
    ((xᵉ yᵉ : Xᵉ) → μᵉ xᵉ yᵉ ＝ᵉ μᵉ yᵉ xᵉ) → ((xᵉ yᵉ zᵉ : Xᵉ) → μᵉ (μᵉ xᵉ yᵉ) zᵉ ＝ᵉ μᵉ xᵉ (μᵉ yᵉ zᵉ)) →
    interchange-lawᵉ μᵉ
  interchange-law-commutative-and-associativeᵉ Cᵉ Aᵉ xᵉ yᵉ uᵉ vᵉ =
    ( Aᵉ xᵉ yᵉ (μᵉ uᵉ vᵉ)) ∙ᵉ
    ( ( apᵉ
        ( μᵉ xᵉ)
        ( (invᵉ (Aᵉ yᵉ uᵉ vᵉ)) ∙ᵉ ((apᵉ (λ zᵉ → μᵉ zᵉ vᵉ) (Cᵉ yᵉ uᵉ)) ∙ᵉ (Aᵉ uᵉ yᵉ vᵉ)))) ∙ᵉ
      ( invᵉ (Aᵉ xᵉ uᵉ (μᵉ yᵉ vᵉ))))
```