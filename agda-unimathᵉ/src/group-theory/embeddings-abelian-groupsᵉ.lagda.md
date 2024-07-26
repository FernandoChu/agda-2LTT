# Embeddings of abelian groups

```agda
module group-theory.embeddings-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.embeddingsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.embeddings-groupsᵉ
open import group-theory.homomorphisms-abelian-groupsᵉ
open import group-theory.subgroups-abelian-groupsᵉ
```

</details>

## Idea

Embeddingsᵉ ofᵉ groupsᵉ areᵉ groupᵉ homomorphismsᵉ ofᵉ whichᵉ theᵉ underlyingᵉ mapᵉ isᵉ anᵉ
embeddingᵉ

## Definitions

### Embeddings of abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  is-emb-hom-Abᵉ : (hom-Abᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-emb-hom-Abᵉ = is-emb-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  emb-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  emb-Abᵉ = emb-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  hom-emb-Abᵉ : emb-Abᵉ → hom-Abᵉ Aᵉ Bᵉ
  hom-emb-Abᵉ = hom-emb-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  map-emb-hom-Abᵉ : emb-Abᵉ → type-Abᵉ Aᵉ → type-Abᵉ Bᵉ
  map-emb-hom-Abᵉ = map-emb-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  is-emb-map-emb-hom-Abᵉ : (fᵉ : emb-Abᵉ) → is-embᵉ (map-emb-hom-Abᵉ fᵉ)
  is-emb-map-emb-hom-Abᵉ =
    is-emb-map-emb-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)
```

### The type of all embeddings into an abelian group

```agda
emb-Ab-Sliceᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
emb-Ab-Sliceᵉ lᵉ Aᵉ = emb-Group-Sliceᵉ lᵉ (group-Abᵉ Aᵉ)

emb-ab-slice-Subgroup-Abᵉ :
  { l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) →
  Subgroup-Abᵉ l2ᵉ Aᵉ → emb-Ab-Sliceᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ
emb-ab-slice-Subgroup-Abᵉ Aᵉ = emb-group-slice-Subgroupᵉ (group-Abᵉ Aᵉ)
```