# Lifting operations

```agda
module orthogonal-factorization-systems.lifting-operationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.sectionsᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.pullback-homᵉ
```

</details>

## Idea

Givenᵉ twoᵉ maps,ᵉ `fᵉ : Aᵉ → X`ᵉ andᵉ `gᵉ : Bᵉ → Y`,ᵉ aᵉ _liftingᵉ operationᵉ betweenᵉ `f`ᵉ
andᵉ `g`ᵉ_ isᵉ aᵉ choiceᵉ ofᵉ liftingᵉ squareᵉ forᵉ everyᵉ commutingᵉ squareᵉ

```text
  Aᵉ ------>ᵉ Bᵉ
  |         |
 f|ᵉ         |gᵉ
  ∨ᵉ         ∨ᵉ
  Xᵉ ------>ᵉ Y.ᵉ
```

Givenᵉ aᵉ liftingᵉ operationᵉ weᵉ canᵉ sayᵉ thatᵉ `f`ᵉ hasᵉ aᵉ _leftᵉ liftingᵉ structureᵉ_
with respectᵉ to `g`ᵉ andᵉ thatᵉ `g`ᵉ hasᵉ aᵉ _rightᵉ liftingᵉ structureᵉ_ with respectᵉ to
`f`.ᵉ

**Note**ᵉ: Thisᵉ isᵉ theᵉ Curry–Howardᵉ interpretationᵉ ofᵉ whatᵉ isᵉ classicallyᵉ calledᵉ
_liftingᵉ properties_.ᵉ However,ᵉ theseᵉ areᵉ generallyᵉ additionalᵉ structureᵉ onᵉ theᵉ
maps.ᵉ Forᵉ theᵉ proof-irrelevantᵉ notionᵉ seeᵉ
[mereᵉ liftingᵉ properties](orthogonal-factorization-systems.mere-lifting-properties.md).ᵉ

## Definition

Weᵉ defineᵉ liftingᵉ operationsᵉ to beᵉ [sections](foundation-core.sections.mdᵉ) ofᵉ
theᵉ [pullback-hom](orthogonal-factorization-systems.pullback-hom.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ)
  where

  diagonal-liftᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  diagonal-liftᵉ = sectionᵉ (pullback-homᵉ fᵉ gᵉ)

  _⧄ᵉ_ = diagonal-liftᵉ

  map-diagonal-liftᵉ : diagonal-liftᵉ → hom-arrowᵉ fᵉ gᵉ → Xᵉ → Bᵉ
  map-diagonal-liftᵉ = pr1ᵉ

  is-section-map-diagonal-liftᵉ :
    (dᵉ : diagonal-liftᵉ) → (pullback-homᵉ fᵉ gᵉ ∘ᵉ map-diagonal-liftᵉ dᵉ) ~ᵉ idᵉ
  is-section-map-diagonal-liftᵉ = pr2ᵉ
```