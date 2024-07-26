# Mere embeddings

```agda
module foundation.mere-embeddingsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cantor-schroder-bernstein-escardoᵉ
open import foundation.embeddingsᵉ
open import foundation.law-of-excluded-middleᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ

open import order-theory.large-preordersᵉ
```

</details>

## Definition

```agda
mere-emb-Propᵉ : {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
mere-emb-Propᵉ Xᵉ Yᵉ = trunc-Propᵉ (Xᵉ ↪ᵉ Yᵉ)

mere-embᵉ : {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
mere-embᵉ Xᵉ Yᵉ = type-Propᵉ (mere-emb-Propᵉ Xᵉ Yᵉ)

is-prop-mere-embᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : UUᵉ l2ᵉ) → is-propᵉ (mere-embᵉ Xᵉ Yᵉ)
is-prop-mere-embᵉ Xᵉ Yᵉ = is-prop-type-Propᵉ (mere-emb-Propᵉ Xᵉ Yᵉ)
```

## Properties

### Types equipped with mere embeddings form a preordering

```agda
refl-mere-embᵉ : {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) → mere-embᵉ Xᵉ Xᵉ
refl-mere-embᵉ Xᵉ = unit-trunc-Propᵉ id-embᵉ

transitive-mere-embᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Zᵉ : UUᵉ l3ᵉ} →
  mere-embᵉ Yᵉ Zᵉ → mere-embᵉ Xᵉ Yᵉ → mere-embᵉ Xᵉ Zᵉ
transitive-mere-embᵉ gᵉ fᵉ =
  apply-universal-property-trunc-Propᵉ gᵉ
    ( mere-emb-Propᵉ _ _)
    ( λ g'ᵉ →
      apply-universal-property-trunc-Propᵉ fᵉ
        ( mere-emb-Propᵉ _ _)
        ( λ f'ᵉ → unit-trunc-Propᵉ (comp-embᵉ g'ᵉ f'ᵉ)))

mere-emb-Large-Preorderᵉ : Large-Preorderᵉ lsuc (_⊔ᵉ_)
type-Large-Preorderᵉ mere-emb-Large-Preorderᵉ lᵉ = UUᵉ lᵉ
leq-prop-Large-Preorderᵉ mere-emb-Large-Preorderᵉ = mere-emb-Propᵉ
refl-leq-Large-Preorderᵉ mere-emb-Large-Preorderᵉ = refl-mere-embᵉ
transitive-leq-Large-Preorderᵉ mere-emb-Large-Preorderᵉ Xᵉ Yᵉ Zᵉ =
  transitive-mere-embᵉ
```

### Assuming excluded middle, if there are mere embeddings between `A` and `B` in both directions, then there is a mere equivalence between them

```agda
antisymmetric-mere-embᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
  LEMᵉ (l1ᵉ ⊔ l2ᵉ) → mere-embᵉ Xᵉ Yᵉ → mere-embᵉ Yᵉ Xᵉ → mere-equivᵉ Xᵉ Yᵉ
antisymmetric-mere-embᵉ lemᵉ fᵉ gᵉ =
  apply-universal-property-trunc-Propᵉ fᵉ
    ( mere-equiv-Propᵉ _ _)
    ( λ f'ᵉ →
      apply-universal-property-trunc-Propᵉ gᵉ
        ( mere-equiv-Propᵉ _ _)
        ( λ g'ᵉ → unit-trunc-Propᵉ (Cantor-Schröder-Bernstein-Escardóᵉ lemᵉ f'ᵉ g'ᵉ)))
```