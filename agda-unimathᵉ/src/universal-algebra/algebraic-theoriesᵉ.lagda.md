# Algebraic theories

```agda
module universal-algebra.algebraic-theoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import universal-algebra.abstract-equations-over-signaturesᵉ
open import universal-algebra.signaturesᵉ
```

</details>

## Idea

Anᵉ algebraicᵉ theoryᵉ isᵉ aᵉ collectionᵉ ofᵉ abstract equationsᵉ overᵉ aᵉ signatureᵉ `S`ᵉ
thatᵉ weᵉ considerᵉ to 'hold'ᵉ in theᵉ theory.ᵉ Itᵉ isᵉ algebraicᵉ in theᵉ senseᵉ thatᵉ weᵉ
onlyᵉ requireᵉ equationsᵉ involvingᵉ functionᵉ symbolsᵉ fromᵉ theᵉ signature,ᵉ in
contrastᵉ to,ᵉ say,ᵉ requiringᵉ additionalᵉ typesᵉ ofᵉ relations.ᵉ

## Definitions

### Theories

```agda
module _
  {l1ᵉ : Level} (Sgᵉ : signatureᵉ l1ᵉ)
  where

  Theoryᵉ : (l2ᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  Theoryᵉ l2ᵉ = Σᵉ (UUᵉ l2ᵉ) (λ Bᵉ → (Bᵉ → Abstract-Equationᵉ Sgᵉ))

  index-Theoryᵉ : {l2ᵉ : Level} → Theoryᵉ l2ᵉ → UUᵉ l2ᵉ
  index-Theoryᵉ = pr1ᵉ

  index-Abstract-Equation-Theoryᵉ :
    { l2ᵉ : Level}
    ( Thᵉ : Theoryᵉ l2ᵉ) →
    ( index-Theoryᵉ Thᵉ) →
    Abstract-Equationᵉ Sgᵉ
  index-Abstract-Equation-Theoryᵉ Thᵉ eᵉ = pr2ᵉ Thᵉ eᵉ
```