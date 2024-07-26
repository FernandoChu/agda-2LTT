# Type duality of finite types

```agda
module univalent-combinatorics.type-dualityᵉ where

open import foundation.type-dualityᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.full-subtypesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-function-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.propositionsᵉ
open import foundation.structureᵉ
open import foundation.structured-type-dualityᵉ
open import foundation.surjective-mapsᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.fibers-of-mapsᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.inhabited-finite-typesᵉ
```

</details>

## Properties

### Subtype duality

```agda
equiv-surjection-𝔽-family-finite-inhabited-typeᵉ :
  {lᵉ : Level} (Aᵉ : 𝔽ᵉ lᵉ) (Bᵉ : 𝔽ᵉ lᵉ) →
  ( (type-𝔽ᵉ Aᵉ ↠ᵉ type-𝔽ᵉ Bᵉ) ≃ᵉ
    ( Σᵉ ( (type-𝔽ᵉ Bᵉ) → Inhabited-𝔽ᵉ lᵉ)
        ( λ Yᵉ → (type-𝔽ᵉ Aᵉ) ≃ᵉ Σᵉ (type-𝔽ᵉ Bᵉ) (λ bᵉ → type-Inhabited-𝔽ᵉ (Yᵉ bᵉ)))))
equiv-surjection-𝔽-family-finite-inhabited-typeᵉ {lᵉ} Aᵉ Bᵉ =
  ( ( equiv-Σᵉ
      ( λ Yᵉ → type-𝔽ᵉ Aᵉ ≃ᵉ Σᵉ (type-𝔽ᵉ Bᵉ) (λ bᵉ → type-Inhabited-𝔽ᵉ (Yᵉ bᵉ)))
      ( equiv-postcompᵉ
        ( type-𝔽ᵉ Bᵉ)
        ( inv-associative-Σᵉ ( UUᵉ lᵉ) is-finiteᵉ ( λ Xᵉ → is-inhabitedᵉ (pr1ᵉ Xᵉ)) ∘eᵉ
          equiv-Σᵉ
            ( λ zᵉ → is-finiteᵉ zᵉ ×ᵉ is-inhabitedᵉ zᵉ)
            ( id-equivᵉ)
            ( λ _ → commutative-productᵉ)))
      ( λ bᵉ → id-equivᵉ)) ∘eᵉ
    ( ( equiv-fixed-Slice-structureᵉ
        ( λ xᵉ → (is-inhabitedᵉ xᵉ) ×ᵉ (is-finiteᵉ xᵉ))
        ( type-𝔽ᵉ Aᵉ)
        ( type-𝔽ᵉ Bᵉ)) ∘eᵉ
      ( ( equiv-Σᵉ
          ( structure-mapᵉ (λ xᵉ → is-inhabitedᵉ xᵉ ×ᵉ is-finiteᵉ xᵉ))
          ( id-equivᵉ)
          ( λ _ → inv-equivᵉ distributive-Π-Σᵉ)) ∘eᵉ
        ( ( associative-Σᵉ
            ( type-𝔽ᵉ Aᵉ → type-𝔽ᵉ Bᵉ)
            ( structure-mapᵉ is-inhabitedᵉ)
            ( _)) ∘eᵉ
          ( ( inv-equivᵉ
              ( equiv-inclusion-is-full-subtypeᵉ
                ( λ fᵉ →
                  Π-Propᵉ (type-𝔽ᵉ Bᵉ) (λ bᵉ → is-finite-Propᵉ (fiberᵉ (pr1ᵉ fᵉ) bᵉ)))
                ( λ fᵉ →
                  is-finite-fiberᵉ
                    ( pr1ᵉ fᵉ)
                    ( is-finite-type-𝔽ᵉ Aᵉ)
                    ( is-finite-type-𝔽ᵉ Bᵉ)))))))))

Slice-Surjection-𝔽ᵉ : (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
Slice-Surjection-𝔽ᵉ lᵉ Aᵉ = Σᵉ (𝔽ᵉ lᵉ) (λ Xᵉ → (type-𝔽ᵉ Xᵉ) ↠ᵉ type-𝔽ᵉ Aᵉ)

equiv-Fiber-trunc-Prop-𝔽ᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) →
  Slice-Surjection-𝔽ᵉ (l1ᵉ ⊔ lᵉ) Aᵉ ≃ᵉ (type-𝔽ᵉ Aᵉ → Inhabited-𝔽ᵉ (l1ᵉ ⊔ lᵉ))
equiv-Fiber-trunc-Prop-𝔽ᵉ lᵉ {l1ᵉ} Aᵉ =
  ( ( equiv-Πᵉ
      ( λ _ → Inhabited-𝔽ᵉ _)
      ( id-equivᵉ)
      ( λ aᵉ → inv-associative-Σᵉ _ _ _) ∘eᵉ
      ( ( equiv-Fiber-structureᵉ
          ( lᵉ)
          ( λ Xᵉ → is-finiteᵉ Xᵉ ×ᵉ is-inhabitedᵉ Xᵉ) (type-𝔽ᵉ Aᵉ)))) ∘eᵉ
    ( ( equiv-Σᵉ
        ( _)
        ( id-equivᵉ)
        ( λ Xᵉ →
          ( equiv-Σᵉ
            ( _)
            ( id-equivᵉ)
            ( λ fᵉ →
              ( inv-equivᵉ distributive-Π-Σᵉ) ∘eᵉ
              ( equiv-Σ-equiv-baseᵉ
                ( _)
                ( inv-equivᵉ
                  ( equiv-is-finite-domain-is-finite-fiberᵉ Aᵉ fᵉ)))))) ∘eᵉ
      ( ( equiv-Σᵉ
          ( _)
          ( id-equivᵉ)
          ( λ _ → equiv-left-swap-Σᵉ)) ∘eᵉ
        ( associative-Σᵉ (UUᵉ (lᵉ ⊔ l1ᵉ)) (is-finiteᵉ) _)))))
```