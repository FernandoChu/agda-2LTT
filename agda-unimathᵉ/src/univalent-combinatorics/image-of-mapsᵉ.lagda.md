# The image of a map

```agda
module univalent-combinatorics.image-of-mapsᵉ where

open import foundation.imagesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.subtypesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  (Kᵉ : is-finiteᵉ Aᵉ)
  where

  abstract
    is-finite-codomainᵉ :
      is-surjectiveᵉ fᵉ → has-decidable-equalityᵉ Bᵉ → is-finiteᵉ Bᵉ
    is-finite-codomainᵉ Hᵉ dᵉ =
      is-finite-base-is-finite-Σ-merely-inhabitedᵉ
        ( is-set-has-decidable-equalityᵉ dᵉ)
        ( Hᵉ)
        ( is-finite-equiv'ᵉ (equiv-total-fiberᵉ fᵉ) Kᵉ)
        ( λ bᵉ → is-finite-Σᵉ Kᵉ (λ aᵉ → is-finite-eqᵉ dᵉ))

abstract
  is-finite-imᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} (Kᵉ : is-finiteᵉ Aᵉ) →
    has-decidable-equalityᵉ Bᵉ → is-finiteᵉ (imᵉ fᵉ)
  is-finite-imᵉ {fᵉ = fᵉ} Kᵉ dᵉ =
    is-finite-codomainᵉ Kᵉ
      ( is-surjective-map-unit-imᵉ fᵉ)
      ( λ xᵉ yᵉ →
        is-decidable-equivᵉ
          ( extensionality-type-subtype'ᵉ (λ uᵉ → trunc-Propᵉ (fiberᵉ fᵉ uᵉ)) xᵉ yᵉ)
          ( dᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ)))
```