# Signatures

```agda
module universal-algebra.signaturesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ signatureᵉ isᵉ aᵉ collectionᵉ ofᵉ functionᵉ symbolsᵉ with givenᵉ arities.ᵉ

## Definitions

### Signatures

```agda
signatureᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
signatureᵉ (lᵉ) = Σᵉ (UUᵉ lᵉ) (λ operationsᵉ → (operationsᵉ → ℕᵉ))

operation-signatureᵉ : {lᵉ : Level} → signatureᵉ lᵉ → UUᵉ lᵉ
operation-signatureᵉ Sgᵉ = pr1ᵉ Sgᵉ

arity-operation-signatureᵉ :
  { lᵉ : Level} →
  ( Sgᵉ : signatureᵉ lᵉ) →
  ( operation-signatureᵉ Sgᵉ → ℕᵉ)
arity-operation-signatureᵉ Sgᵉ = pr2ᵉ Sgᵉ
```

### Extension of signatures

```agda
is-extension-signatureᵉ :
  { l1ᵉ l2ᵉ : Level} →
  signatureᵉ l1ᵉ → signatureᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-extension-signatureᵉ Sg1ᵉ Sg2ᵉ =
  Σᵉ ( operation-signatureᵉ Sg2ᵉ → operation-signatureᵉ Sg1ᵉ)
    ( λ fᵉ → is-embᵉ fᵉ ×ᵉ
      ( ( opᵉ : operation-signatureᵉ Sg2ᵉ) →
        arity-operation-signatureᵉ Sg2ᵉ opᵉ ＝ᵉ
          arity-operation-signatureᵉ Sg1ᵉ (fᵉ opᵉ)))

emb-extension-signatureᵉ :
  { l1ᵉ l2ᵉ : Level} →
  ( Sg1ᵉ : signatureᵉ l1ᵉ) →
  ( Sg2ᵉ : signatureᵉ l2ᵉ) →
  is-extension-signatureᵉ Sg1ᵉ Sg2ᵉ →
  ( operation-signatureᵉ Sg2ᵉ → operation-signatureᵉ Sg1ᵉ)
emb-extension-signatureᵉ Sg1ᵉ Sg2ᵉ extᵉ = pr1ᵉ extᵉ

is-emb-extension-signatureᵉ :
  { l1ᵉ l2ᵉ : Level} →
  ( Sg1ᵉ : signatureᵉ l1ᵉ) →
  ( Sg2ᵉ : signatureᵉ l2ᵉ) →
  ( extᵉ : is-extension-signatureᵉ Sg1ᵉ Sg2ᵉ) →
  is-embᵉ (emb-extension-signatureᵉ Sg1ᵉ Sg2ᵉ extᵉ)
is-emb-extension-signatureᵉ Sg1ᵉ Sg2ᵉ extᵉ = pr1ᵉ (pr2ᵉ extᵉ)

arity-preserved-extension-signatureᵉ :
  { l1ᵉ l2ᵉ : Level} →
  ( Sg1ᵉ : signatureᵉ l1ᵉ) →
  ( Sg2ᵉ : signatureᵉ l2ᵉ) →
  ( extᵉ : is-extension-signatureᵉ Sg1ᵉ Sg2ᵉ) →
  ( opᵉ : operation-signatureᵉ Sg2ᵉ) →
  arity-operation-signatureᵉ Sg2ᵉ opᵉ ＝ᵉ
    arity-operation-signatureᵉ Sg1ᵉ
      ( emb-extension-signatureᵉ Sg1ᵉ Sg2ᵉ extᵉ opᵉ)
arity-preserved-extension-signatureᵉ Sg1ᵉ Sg2ᵉ extᵉ = pr2ᵉ (pr2ᵉ extᵉ)
```