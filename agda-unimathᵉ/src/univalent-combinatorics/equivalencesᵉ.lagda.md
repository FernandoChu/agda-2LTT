# Equivalences between finite types

```agda
module univalent-combinatorics.equivalencesᵉ where

open import foundation.equivalencesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.embeddingsᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.surjective-mapsᵉ
```

</details>

## Properties

### For a map between finite types, being an equivalence is decidable

```agda
is-decidable-is-equiv-is-finiteᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-finiteᵉ Aᵉ → is-finiteᵉ Bᵉ → is-decidableᵉ (is-equivᵉ fᵉ)
is-decidable-is-equiv-is-finiteᵉ fᵉ HAᵉ HBᵉ =
  is-decidable-iffᵉ
    ( λ pᵉ → is-equiv-is-emb-is-surjectiveᵉ (pr1ᵉ pᵉ) (pr2ᵉ pᵉ))
    ( λ Kᵉ → pairᵉ (is-surjective-is-equivᵉ Kᵉ) (is-emb-is-equivᵉ Kᵉ))
    ( is-decidable-productᵉ
      ( is-decidable-is-surjective-is-finiteᵉ fᵉ HAᵉ HBᵉ)
      ( is-decidable-is-emb-is-finiteᵉ fᵉ HAᵉ HBᵉ))
```