# Embeddings of groups

```agda
module group-theory.embeddings-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.subgroupsᵉ
```

</details>

## Idea

Embeddingsᵉ ofᵉ groupsᵉ areᵉ groupᵉ homomorphismsᵉ ofᵉ whichᵉ theᵉ underlyingᵉ mapᵉ isᵉ anᵉ
embeddingᵉ

## Definitions

### Embeddings of groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  where

  is-emb-hom-Groupᵉ : (hom-Groupᵉ Gᵉ Hᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-emb-hom-Groupᵉ hᵉ = is-embᵉ (map-hom-Groupᵉ Gᵉ Hᵉ hᵉ)

  emb-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  emb-Groupᵉ = Σᵉ (hom-Groupᵉ Gᵉ Hᵉ) is-emb-hom-Groupᵉ

  hom-emb-Groupᵉ : emb-Groupᵉ → hom-Groupᵉ Gᵉ Hᵉ
  hom-emb-Groupᵉ = pr1ᵉ

  map-emb-hom-Groupᵉ : emb-Groupᵉ → type-Groupᵉ Gᵉ → type-Groupᵉ Hᵉ
  map-emb-hom-Groupᵉ fᵉ = map-hom-Groupᵉ Gᵉ Hᵉ (hom-emb-Groupᵉ fᵉ)

  is-emb-map-emb-hom-Groupᵉ : (fᵉ : emb-Groupᵉ) → is-embᵉ (map-emb-hom-Groupᵉ fᵉ)
  is-emb-map-emb-hom-Groupᵉ = pr2ᵉ
```

### The type of all embeddings into a group

```agda
emb-Group-Sliceᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
emb-Group-Sliceᵉ lᵉ Gᵉ = Σᵉ ( Groupᵉ lᵉ) (λ Hᵉ → emb-Groupᵉ Hᵉ Gᵉ)

emb-group-slice-Subgroupᵉ :
  { l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
  Subgroupᵉ l2ᵉ Gᵉ → emb-Group-Sliceᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
pr1ᵉ (emb-group-slice-Subgroupᵉ Gᵉ Pᵉ) = group-Subgroupᵉ Gᵉ Pᵉ
pr1ᵉ (pr2ᵉ (emb-group-slice-Subgroupᵉ Gᵉ Pᵉ)) = hom-inclusion-Subgroupᵉ Gᵉ Pᵉ
pr2ᵉ (pr2ᵉ (emb-group-slice-Subgroupᵉ Gᵉ Pᵉ)) =
  is-emb-inclusion-Subgroupᵉ Gᵉ Pᵉ
```