# Binary embeddings

```agda
module foundation.binary-embeddingsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
```

</details>

## Idea

Aᵉ binaryᵉ operationᵉ `fᵉ : Aᵉ → Bᵉ → C`ᵉ isᵉ saidᵉ to beᵉ aᵉ binaryᵉ embeddingᵉ ifᵉ theᵉ
functionsᵉ `λᵉ xᵉ → fᵉ xᵉ b`ᵉ andᵉ `λᵉ yᵉ → fᵉ aᵉ y`ᵉ areᵉ embeddingsᵉ forᵉ eachᵉ `aᵉ : A`ᵉ andᵉ
`bᵉ : B`ᵉ respectively.ᵉ

## Definition

```agda
is-binary-embᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} →
  (Aᵉ → Bᵉ → Cᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
is-binary-embᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} fᵉ =
  {xᵉ x'ᵉ : Aᵉ} {yᵉ y'ᵉ : Bᵉ} →
    is-binary-equivᵉ (λ (pᵉ : xᵉ ＝ᵉ x'ᵉ) (qᵉ : yᵉ ＝ᵉ y'ᵉ) → ap-binaryᵉ fᵉ pᵉ qᵉ)
```

## Properties

### Any binary equivalence is a binary embedding

```agda
is-emb-fix-left-is-binary-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ) →
  is-binary-equivᵉ fᵉ → {aᵉ : Aᵉ} → is-embᵉ (fix-leftᵉ fᵉ aᵉ)
is-emb-fix-left-is-binary-equivᵉ fᵉ Hᵉ {aᵉ} =
  is-emb-is-equivᵉ (is-equiv-fix-leftᵉ fᵉ Hᵉ)

is-emb-fix-right-is-binary-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ) →
  is-binary-equivᵉ fᵉ → {bᵉ : Bᵉ} → is-embᵉ (fix-rightᵉ fᵉ bᵉ)
is-emb-fix-right-is-binary-equivᵉ fᵉ Hᵉ {bᵉ} =
  is-emb-is-equivᵉ (is-equiv-fix-rightᵉ fᵉ Hᵉ)

is-binary-emb-is-binary-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {fᵉ : Aᵉ → Bᵉ → Cᵉ} →
  is-binary-equivᵉ fᵉ → is-binary-embᵉ fᵉ
is-binary-emb-is-binary-equivᵉ {fᵉ = fᵉ} Hᵉ {xᵉ} {x'ᵉ} {yᵉ} {y'ᵉ} =
  pairᵉ
    ( λ qᵉ →
      is-equiv-left-map-triangleᵉ
        ( λ pᵉ → ap-binaryᵉ fᵉ pᵉ qᵉ)
        ( concat'ᵉ (fᵉ xᵉ yᵉ) (apᵉ (fix-leftᵉ fᵉ x'ᵉ) qᵉ))
        ( λ pᵉ → apᵉ (fix-rightᵉ fᵉ yᵉ) pᵉ)
        ( λ pᵉ → triangle-ap-binaryᵉ fᵉ pᵉ qᵉ)
        ( is-emb-fix-right-is-binary-equivᵉ fᵉ Hᵉ xᵉ x'ᵉ)
        ( is-equiv-concat'ᵉ (fᵉ xᵉ yᵉ) (apᵉ (fix-leftᵉ fᵉ x'ᵉ) qᵉ)))
    ( λ pᵉ →
      is-equiv-left-map-triangleᵉ
        ( λ qᵉ → ap-binaryᵉ fᵉ pᵉ qᵉ)
        ( concatᵉ (apᵉ (fix-rightᵉ fᵉ yᵉ) pᵉ) (fᵉ x'ᵉ y'ᵉ))
        ( λ qᵉ → apᵉ (fix-leftᵉ fᵉ x'ᵉ) qᵉ)
        ( λ qᵉ → triangle-ap-binaryᵉ fᵉ pᵉ qᵉ)
        ( is-emb-fix-left-is-binary-equivᵉ fᵉ Hᵉ yᵉ y'ᵉ)
        ( is-equiv-concatᵉ (apᵉ (fix-rightᵉ fᵉ yᵉ) pᵉ) (fᵉ x'ᵉ y'ᵉ)))
```