# Hereditary W-types

```agda
module trees.hereditary-w-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.universe-levelsᵉ

open import trees.binary-w-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ `A`ᵉ andᵉ twoᵉ typeᵉ familiesᵉ `B`ᵉ andᵉ `C`ᵉ overᵉ `A`.ᵉ Thenᵉ weᵉ obtainᵉ
theᵉ polynomialᵉ functorᵉ

```text
  Xᵉ Yᵉ ↦ᵉ Σᵉ (aᵉ : A),ᵉ (Bᵉ aᵉ → Xᵉ) ×ᵉ (Cᵉ aᵉ → Yᵉ)
```

in twoᵉ variablesᵉ `X`ᵉ andᵉ `Y`.ᵉ Byᵉ fixingᵉ eitherᵉ `X`ᵉ orᵉ `Y`,ᵉ weᵉ obtainᵉ twoᵉ
[polynomialᵉ endofunctors](trees.polynomial-endofunctors.mdᵉ) givenᵉ byᵉ

```text
  Yᵉ ↦ᵉ Σᵉ (aᵉ : A),ᵉ (Bᵉ aᵉ → Xᵉ) ×ᵉ (Cᵉ aᵉ → Yᵉ)
```

andᵉ

```text
  Xᵉ ↦ᵉ Σᵉ (aᵉ : A),ᵉ (Bᵉ aᵉ → Xᵉ) ×ᵉ (Cᵉ aᵉ → Y),ᵉ
```

respectively.ᵉ Theᵉ typeᵉ `left-𝕎`ᵉ isᵉ obtainedᵉ byᵉ lettingᵉ theᵉ leftᵉ argumentᵉ varyᵉ
andᵉ fixingᵉ theᵉ rightᵉ argument,ᵉ i.e.,ᵉ itᵉ isᵉ theᵉ inductive typeᵉ generatedᵉ byᵉ

```text
  make-left-𝕎ᵉ : (aᵉ : Aᵉ) → (Bᵉ aᵉ → left-𝕎ᵉ) → (Cᵉ aᵉ → Yᵉ) → left-𝕎.ᵉ
```

Similarly,ᵉ theᵉ typeᵉ `right-𝕎`ᵉ isᵉ obtainedᵉ byᵉ fixingᵉ theᵉ leftᵉ argumentᵉ andᵉ
varyingᵉ theᵉ rightᵉ argument,ᵉ i.e.,ᵉ itᵉ isᵉ theᵉ inductive typeᵉ generatedᵉ byᵉ

```text
  make-right-𝕎ᵉ : (aᵉ : Aᵉ) → (Bᵉ aᵉ → Xᵉ) → (Cᵉ aᵉ → right-𝕎ᵉ) → right-𝕎.ᵉ
```

Thusᵉ weᵉ obtainᵉ twoᵉ operationsᵉ `left-𝕎`ᵉ andᵉ `right-𝕎`.ᵉ Theᵉ leftᵉ andᵉ rightᵉ
{{#conceptᵉ "hereditaryᵉ W-type"ᵉ Agda=left-hereditary-𝕎ᵉ Agda=right-hereditary-𝕎ᵉ}}
areᵉ theᵉ leastᵉ fixedᵉ pointsᵉ forᵉ theᵉ operationsᵉ `left-𝕎`ᵉ andᵉ `right-𝕎`ᵉ
respectively.ᵉ Thatᵉ is,ᵉ weᵉ defineᵉ `left-hereditary-𝕎`ᵉ asᵉ theᵉ inductive typeᵉ
generatedᵉ byᵉ

```text
  make-left-hereditary-𝕎ᵉ : left-𝕎ᵉ left-hereditary-𝕎ᵉ → left-hereditary-𝕎.ᵉ
```

andᵉ weᵉ defineᵉ `right-hereditary-𝕎`ᵉ asᵉ theᵉ inductive typeᵉ generatedᵉ byᵉ

```text
  make-right-hereditary-𝕎ᵉ : right-𝕎ᵉ right-hereditary-𝕎ᵉ → right-hereditary-𝕎.ᵉ
```

Weᵉ willᵉ constructᵉ equivalencesᵉ

```text
  left-hereditary-𝕎ᵉ ≃ᵉ binary-𝕎ᵉ
```

andᵉ

```text
  right-hereditary-𝕎ᵉ ≃ᵉ binary-𝕎,ᵉ
```

showingᵉ thatᵉ bothᵉ theᵉ leftᵉ andᵉ rightᵉ hereditaryᵉ W-typesᵉ areᵉ equivalentᵉ to theᵉ
binaryᵉ W-typeᵉ associatedᵉ to `B`ᵉ andᵉ `C`.ᵉ

### Motivating example

Ifᵉ weᵉ chooseᵉ `Aᵉ :=ᵉ Finᵉ 2`ᵉ andᵉ

```text
  Bᵉ 0 :=ᵉ emptyᵉ        Cᵉ 0 :=ᵉ emptyᵉ
  Bᵉ 1 :=ᵉ unitᵉ         Cᵉ 1 :=ᵉ unit,ᵉ
```

thenᵉ theᵉ leftᵉ W-typeᵉ `left-𝕎ᵉ Bᵉ C`ᵉ isᵉ equivalentᵉ to theᵉ inductive typeᵉ generatedᵉ
byᵉ

```text
  nilᵉ : left-𝕎ᵉ
  snocᵉ : left-𝕎ᵉ → Yᵉ → left-𝕎,ᵉ
```

whichᵉ isᵉ equivalentᵉ to theᵉ typeᵉ `list`ᵉ ofᵉ [lists](lists.lists.md).ᵉ Theᵉ leftᵉ
hereditaryᵉ W-typeᵉ `left-hereditary-𝕎`ᵉ isᵉ thenᵉ equivalentᵉ to theᵉ typeᵉ ofᵉ planeᵉ
trees.ᵉ Furthermore,ᵉ in thisᵉ caseᵉ theᵉ binaryᵉ W-typeᵉ associatedᵉ to `B`ᵉ andᵉ `C`ᵉ isᵉ
equivalentᵉ to theᵉ inductive typeᵉ generatedᵉ byᵉ

```text
  leafᵉ : left-hereditary-𝕎ᵉ
  nodeᵉ : left-hereditary-𝕎ᵉ → left-hereditary-𝕎ᵉ → left-hereditary-𝕎.ᵉ
```

Thusᵉ weᵉ seeᵉ thatᵉ theᵉ equivalenceᵉ `left-hereditary-𝕎ᵉ ≃ᵉ binary-𝕎`ᵉ isᵉ aᵉ
generalizationᵉ ofᵉ theᵉ well-knownᵉ equivalenceᵉ ofᵉ planeᵉ treesᵉ andᵉ fullᵉ binaryᵉ
planeᵉ trees,ᵉ whichᵉ isᵉ prominentᵉ in theᵉ studyᵉ ofᵉ theᵉ
[Catalanᵉ numbers](elementary-number-theory.catalan-numbers.md).ᵉ

## Definitions

### Left hereditary W-types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  data left-𝕎ᵉ {l4ᵉ : Level} (Yᵉ : UUᵉ l4ᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ) where
    make-left-𝕎ᵉ : (aᵉ : Aᵉ) → (Bᵉ aᵉ → left-𝕎ᵉ Yᵉ) → (Cᵉ aᵉ → Yᵉ) → left-𝕎ᵉ Yᵉ

  data left-hereditary-𝕎ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) where
    make-left-hereditary-𝕎ᵉ : left-𝕎ᵉ left-hereditary-𝕎ᵉ → left-hereditary-𝕎ᵉ
```

### Right hereditary W-types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  data right-𝕎ᵉ {l4ᵉ : Level} (Xᵉ : UUᵉ l4ᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ) where
    make-right-𝕎ᵉ : (aᵉ : Aᵉ) → (Bᵉ aᵉ → Xᵉ) → (Cᵉ aᵉ → right-𝕎ᵉ Xᵉ) → right-𝕎ᵉ Xᵉ

  data right-hereditary-𝕎ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) where
    make-right-hereditary-𝕎ᵉ : right-𝕎ᵉ right-hereditary-𝕎ᵉ → right-hereditary-𝕎ᵉ
```

## Properties

### The left hereditary W-type is a fixed point for `left-𝕎`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  unpack-left-hereditary-𝕎ᵉ :
    left-hereditary-𝕎ᵉ Bᵉ Cᵉ → left-𝕎ᵉ Bᵉ Cᵉ (left-hereditary-𝕎ᵉ Bᵉ Cᵉ)
  unpack-left-hereditary-𝕎ᵉ (make-left-hereditary-𝕎ᵉ Tᵉ) = Tᵉ

  is-section-unpack-left-hereditary-𝕎ᵉ :
    is-sectionᵉ make-left-hereditary-𝕎ᵉ unpack-left-hereditary-𝕎ᵉ
  is-section-unpack-left-hereditary-𝕎ᵉ (make-left-hereditary-𝕎ᵉ Tᵉ) = reflᵉ

  is-retraction-unpack-left-hereditary-𝕎ᵉ :
    is-retractionᵉ make-left-hereditary-𝕎ᵉ unpack-left-hereditary-𝕎ᵉ
  is-retraction-unpack-left-hereditary-𝕎ᵉ Tᵉ = reflᵉ

  is-equiv-make-left-hereditary-𝕎ᵉ :
    is-equivᵉ make-left-hereditary-𝕎ᵉ
  is-equiv-make-left-hereditary-𝕎ᵉ =
    is-equiv-is-invertibleᵉ
      ( unpack-left-hereditary-𝕎ᵉ)
      ( is-section-unpack-left-hereditary-𝕎ᵉ)
      ( is-retraction-unpack-left-hereditary-𝕎ᵉ)

  equiv-make-left-hereditary-𝕎ᵉ :
    left-𝕎ᵉ Bᵉ Cᵉ (left-hereditary-𝕎ᵉ Bᵉ Cᵉ) ≃ᵉ left-hereditary-𝕎ᵉ Bᵉ Cᵉ
  pr1ᵉ equiv-make-left-hereditary-𝕎ᵉ = make-left-hereditary-𝕎ᵉ
  pr2ᵉ equiv-make-left-hereditary-𝕎ᵉ = is-equiv-make-left-hereditary-𝕎ᵉ
```

### The right hereditary W-type is a fixed point for `right-𝕎`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  unpack-right-hereditary-𝕎ᵉ :
    right-hereditary-𝕎ᵉ Bᵉ Cᵉ → right-𝕎ᵉ Bᵉ Cᵉ (right-hereditary-𝕎ᵉ Bᵉ Cᵉ)
  unpack-right-hereditary-𝕎ᵉ (make-right-hereditary-𝕎ᵉ Tᵉ) = Tᵉ

  is-section-unpack-right-hereditary-𝕎ᵉ :
    is-sectionᵉ make-right-hereditary-𝕎ᵉ unpack-right-hereditary-𝕎ᵉ
  is-section-unpack-right-hereditary-𝕎ᵉ (make-right-hereditary-𝕎ᵉ Tᵉ) = reflᵉ

  is-retraction-unpack-right-hereditary-𝕎ᵉ :
    is-retractionᵉ make-right-hereditary-𝕎ᵉ unpack-right-hereditary-𝕎ᵉ
  is-retraction-unpack-right-hereditary-𝕎ᵉ Tᵉ = reflᵉ

  is-equiv-make-right-hereditary-𝕎ᵉ :
    is-equivᵉ make-right-hereditary-𝕎ᵉ
  is-equiv-make-right-hereditary-𝕎ᵉ =
    is-equiv-is-invertibleᵉ
      ( unpack-right-hereditary-𝕎ᵉ)
      ( is-section-unpack-right-hereditary-𝕎ᵉ)
      ( is-retraction-unpack-right-hereditary-𝕎ᵉ)

  equiv-make-right-hereditary-𝕎ᵉ :
    right-𝕎ᵉ Bᵉ Cᵉ (right-hereditary-𝕎ᵉ Bᵉ Cᵉ) ≃ᵉ right-hereditary-𝕎ᵉ Bᵉ Cᵉ
  pr1ᵉ equiv-make-right-hereditary-𝕎ᵉ = make-right-hereditary-𝕎ᵉ
  pr2ᵉ equiv-make-right-hereditary-𝕎ᵉ = is-equiv-make-right-hereditary-𝕎ᵉ
```

### Left hereditary W-types are binary W-types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  binary-left-hereditary-𝕎ᵉ : left-hereditary-𝕎ᵉ Bᵉ Cᵉ → binary-𝕎ᵉ Bᵉ Cᵉ
  binary-left-hereditary-𝕎ᵉ (make-left-hereditary-𝕎ᵉ (make-left-𝕎ᵉ aᵉ Sᵉ Tᵉ)) =
    make-binary-𝕎ᵉ aᵉ
      ( λ bᵉ → binary-left-hereditary-𝕎ᵉ (make-left-hereditary-𝕎ᵉ (Sᵉ bᵉ)))
      ( λ cᵉ → binary-left-hereditary-𝕎ᵉ (Tᵉ cᵉ))

  left-hereditary-binary-𝕎ᵉ : binary-𝕎ᵉ Bᵉ Cᵉ → left-hereditary-𝕎ᵉ Bᵉ Cᵉ
  left-hereditary-binary-𝕎ᵉ (make-binary-𝕎ᵉ aᵉ Sᵉ Tᵉ) =
    make-left-hereditary-𝕎ᵉ
      ( make-left-𝕎ᵉ aᵉ
        ( λ bᵉ →
          unpack-left-hereditary-𝕎ᵉ Bᵉ Cᵉ (left-hereditary-binary-𝕎ᵉ (Sᵉ bᵉ)))
        ( λ cᵉ → left-hereditary-binary-𝕎ᵉ (Tᵉ cᵉ)))

  is-section-left-hereditary-binary-𝕎ᵉ :
    is-sectionᵉ binary-left-hereditary-𝕎ᵉ left-hereditary-binary-𝕎ᵉ
  is-section-left-hereditary-binary-𝕎ᵉ (make-binary-𝕎ᵉ aᵉ Sᵉ Tᵉ) =
    ap-binaryᵉ
      ( make-binary-𝕎ᵉ aᵉ)
      ( eq-htpyᵉ
        ( λ bᵉ →
          ( apᵉ
            ( binary-left-hereditary-𝕎ᵉ)
            ( is-section-unpack-left-hereditary-𝕎ᵉ Bᵉ Cᵉ
              ( left-hereditary-binary-𝕎ᵉ (Sᵉ bᵉ)))) ∙ᵉ
          ( is-section-left-hereditary-binary-𝕎ᵉ (Sᵉ bᵉ))))
      ( eq-htpyᵉ (λ cᵉ → is-section-left-hereditary-binary-𝕎ᵉ (Tᵉ cᵉ)))

  is-retraction-left-hereditary-binary-𝕎ᵉ :
    is-retractionᵉ binary-left-hereditary-𝕎ᵉ left-hereditary-binary-𝕎ᵉ
  is-retraction-left-hereditary-binary-𝕎ᵉ
    ( make-left-hereditary-𝕎ᵉ (make-left-𝕎ᵉ aᵉ Sᵉ Tᵉ)) =
    apᵉ
      ( make-left-hereditary-𝕎ᵉ)
      ( ap-binaryᵉ
        ( make-left-𝕎ᵉ aᵉ)
        ( eq-htpyᵉ
          ( λ bᵉ →
            apᵉ
              ( unpack-left-hereditary-𝕎ᵉ Bᵉ Cᵉ)
              ( is-retraction-left-hereditary-binary-𝕎ᵉ
                ( make-left-hereditary-𝕎ᵉ (Sᵉ bᵉ)))))
        ( eq-htpyᵉ (λ cᵉ → is-retraction-left-hereditary-binary-𝕎ᵉ (Tᵉ cᵉ))))

  is-equiv-binary-left-hereditary-𝕎ᵉ :
    is-equivᵉ binary-left-hereditary-𝕎ᵉ
  is-equiv-binary-left-hereditary-𝕎ᵉ =
    is-equiv-is-invertibleᵉ
      ( left-hereditary-binary-𝕎ᵉ)
      ( is-section-left-hereditary-binary-𝕎ᵉ)
      ( is-retraction-left-hereditary-binary-𝕎ᵉ)

  equiv-binary-left-hereditary-𝕎ᵉ :
    left-hereditary-𝕎ᵉ Bᵉ Cᵉ ≃ᵉ binary-𝕎ᵉ Bᵉ Cᵉ
  pr1ᵉ equiv-binary-left-hereditary-𝕎ᵉ = binary-left-hereditary-𝕎ᵉ
  pr2ᵉ equiv-binary-left-hereditary-𝕎ᵉ = is-equiv-binary-left-hereditary-𝕎ᵉ
```

### Right hereditary W-types are binary W-types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  binary-right-hereditary-𝕎ᵉ : right-hereditary-𝕎ᵉ Bᵉ Cᵉ → binary-𝕎ᵉ Bᵉ Cᵉ
  binary-right-hereditary-𝕎ᵉ (make-right-hereditary-𝕎ᵉ (make-right-𝕎ᵉ aᵉ Sᵉ Tᵉ)) =
    make-binary-𝕎ᵉ aᵉ
      ( λ bᵉ → binary-right-hereditary-𝕎ᵉ (Sᵉ bᵉ))
      ( λ cᵉ → binary-right-hereditary-𝕎ᵉ (make-right-hereditary-𝕎ᵉ (Tᵉ cᵉ)))

  right-hereditary-binary-𝕎ᵉ : binary-𝕎ᵉ Bᵉ Cᵉ → right-hereditary-𝕎ᵉ Bᵉ Cᵉ
  right-hereditary-binary-𝕎ᵉ (make-binary-𝕎ᵉ aᵉ Sᵉ Tᵉ) =
    make-right-hereditary-𝕎ᵉ
      ( make-right-𝕎ᵉ aᵉ
        ( λ bᵉ → right-hereditary-binary-𝕎ᵉ (Sᵉ bᵉ))
        ( λ cᵉ →
          unpack-right-hereditary-𝕎ᵉ Bᵉ Cᵉ (right-hereditary-binary-𝕎ᵉ (Tᵉ cᵉ))))

  is-section-right-hereditary-binary-𝕎ᵉ :
    is-sectionᵉ binary-right-hereditary-𝕎ᵉ right-hereditary-binary-𝕎ᵉ
  is-section-right-hereditary-binary-𝕎ᵉ (make-binary-𝕎ᵉ aᵉ Sᵉ Tᵉ) =
    ap-binaryᵉ
      ( make-binary-𝕎ᵉ aᵉ)
      ( eq-htpyᵉ (λ bᵉ → is-section-right-hereditary-binary-𝕎ᵉ (Sᵉ bᵉ)))
      ( eq-htpyᵉ
        ( λ cᵉ →
          ( apᵉ
            ( binary-right-hereditary-𝕎ᵉ)
            ( is-section-unpack-right-hereditary-𝕎ᵉ Bᵉ Cᵉ
              ( right-hereditary-binary-𝕎ᵉ (Tᵉ cᵉ)))) ∙ᵉ
          ( is-section-right-hereditary-binary-𝕎ᵉ (Tᵉ cᵉ))))

  is-retraction-right-hereditary-binary-𝕎ᵉ :
    is-retractionᵉ binary-right-hereditary-𝕎ᵉ right-hereditary-binary-𝕎ᵉ
  is-retraction-right-hereditary-binary-𝕎ᵉ
    ( make-right-hereditary-𝕎ᵉ (make-right-𝕎ᵉ aᵉ Sᵉ Tᵉ)) =
    apᵉ
      ( make-right-hereditary-𝕎ᵉ)
      ( ap-binaryᵉ
        ( make-right-𝕎ᵉ aᵉ)
        ( eq-htpyᵉ (λ bᵉ → is-retraction-right-hereditary-binary-𝕎ᵉ (Sᵉ bᵉ)))
        ( eq-htpyᵉ
          ( λ cᵉ →
            apᵉ
              ( unpack-right-hereditary-𝕎ᵉ Bᵉ Cᵉ)
              ( is-retraction-right-hereditary-binary-𝕎ᵉ
                ( make-right-hereditary-𝕎ᵉ (Tᵉ cᵉ))))))

  is-equiv-binary-right-hereditary-𝕎ᵉ :
    is-equivᵉ binary-right-hereditary-𝕎ᵉ
  is-equiv-binary-right-hereditary-𝕎ᵉ =
    is-equiv-is-invertibleᵉ
      ( right-hereditary-binary-𝕎ᵉ)
      ( is-section-right-hereditary-binary-𝕎ᵉ)
      ( is-retraction-right-hereditary-binary-𝕎ᵉ)

  equiv-binary-right-hereditary-𝕎ᵉ :
    right-hereditary-𝕎ᵉ Bᵉ Cᵉ ≃ᵉ binary-𝕎ᵉ Bᵉ Cᵉ
  pr1ᵉ equiv-binary-right-hereditary-𝕎ᵉ = binary-right-hereditary-𝕎ᵉ
  pr2ᵉ equiv-binary-right-hereditary-𝕎ᵉ = is-equiv-binary-right-hereditary-𝕎ᵉ
```