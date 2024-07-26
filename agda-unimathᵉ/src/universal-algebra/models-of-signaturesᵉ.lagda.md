# Models of signatures

```agda
module universal-algebra.models-of-signaturesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectorsᵉ

open import universal-algebra.signaturesᵉ
```

</details>

## Idea

Aᵉ modelᵉ ofᵉ aᵉ signatureᵉ `Sig`ᵉ in aᵉ typeᵉ `A`ᵉ isᵉ aᵉ dependentᵉ functionᵉ thatᵉ assingsᵉ
to eachᵉ functionᵉ symbolᵉ `f`ᵉ ofᵉ arityᵉ `n`ᵉ andᵉ aᵉ vectorᵉ ofᵉ `n`ᵉ elementsᵉ ofᵉ `A`ᵉ anᵉ
elementᵉ ofᵉ `A`.ᵉ

## Definitions

### Models

```agda
module _
  {l1ᵉ : Level} (Sgᵉ : signatureᵉ l1ᵉ)
  where

  is-modelᵉ : {l2ᵉ : Level} → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-modelᵉ Xᵉ =
    ( fᵉ : operation-signatureᵉ Sgᵉ) →
    ( vecᵉ Xᵉ (arity-operation-signatureᵉ Sgᵉ fᵉ) → Xᵉ)

  is-model-signatureᵉ : {l2ᵉ : Level} → (Setᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-model-signatureᵉ Xᵉ = is-modelᵉ (type-Setᵉ Xᵉ)

  Model-Signatureᵉ : (l2ᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  Model-Signatureᵉ l2ᵉ = Σᵉ (Setᵉ l2ᵉ) (λ Xᵉ → is-model-signatureᵉ Xᵉ)

  set-Model-Signatureᵉ : {l2ᵉ : Level} → Model-Signatureᵉ l2ᵉ → Setᵉ l2ᵉ
  set-Model-Signatureᵉ Mᵉ = pr1ᵉ Mᵉ

  is-model-set-Model-Signatureᵉ :
    { l2ᵉ : Level} →
    ( Mᵉ : Model-Signatureᵉ l2ᵉ) →
    is-model-signatureᵉ (set-Model-Signatureᵉ Mᵉ)
  is-model-set-Model-Signatureᵉ Mᵉ = pr2ᵉ Mᵉ

  type-Model-Signatureᵉ : {l2ᵉ : Level} → Model-Signatureᵉ l2ᵉ → UUᵉ l2ᵉ
  type-Model-Signatureᵉ Mᵉ = pr1ᵉ (set-Model-Signatureᵉ Mᵉ)

  is-set-type-Model-Signatureᵉ :
    { l2ᵉ : Level} →
    ( Mᵉ : Model-Signatureᵉ l2ᵉ) →
    is-setᵉ (type-Model-Signatureᵉ Mᵉ)
  is-set-type-Model-Signatureᵉ Mᵉ = pr2ᵉ (set-Model-Signatureᵉ Mᵉ)
```