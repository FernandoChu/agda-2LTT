# Small Composition of species of finite inhabited types

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module species.small-cauchy-composition-species-of-finite-inhabited-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.propositionsᵉ
open import foundation.relaxed-sigma-decompositionsᵉ
open import foundation.sigma-closed-subuniversesᵉ
open import foundation.sigma-decomposition-subuniverseᵉ
open import foundation.subuniversesᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import species.small-cauchy-composition-species-of-types-in-subuniversesᵉ
open import species.species-of-finite-inhabited-typesᵉ

open import univalent-combinatorics.cartesian-product-typesᵉ
open import univalent-combinatorics.decidable-propositionsᵉ
open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.inhabited-finite-typesᵉ
open import univalent-combinatorics.sigma-decompositionsᵉ
open import univalent-combinatorics.small-typesᵉ
```

</details>

## Definition

```agda
equiv-Σ-Decomposition-Inhabited-𝔽-Σ-Decomposition-𝔽ᵉ :
  {lᵉ : Level} (Xᵉ : Inhabited-𝔽ᵉ lᵉ) →
  Σ-Decomposition-𝔽ᵉ lᵉ lᵉ (finite-type-Inhabited-𝔽ᵉ Xᵉ) ≃ᵉ
  Σ-Decomposition-Subuniverseᵉ
    ( is-finite-and-inhabited-Propᵉ)
    ( map-compute-Inhabited-𝔽'ᵉ Xᵉ)
equiv-Σ-Decomposition-Inhabited-𝔽-Σ-Decomposition-𝔽ᵉ Xᵉ =
  ( inv-equivᵉ
    ( equiv-total-is-in-subuniverse-Σ-Decompositionᵉ
      ( is-finite-and-inhabited-Propᵉ)
      ( map-compute-Inhabited-𝔽'ᵉ Xᵉ))) ∘eᵉ
  ( ( equiv-totᵉ
      ( λ Dᵉ →
        equiv-productᵉ
          ( equiv-add-redundant-propᵉ
            ( is-property-is-inhabitedᵉ _)
            ( λ _ →
              map-is-inhabitedᵉ
                ( pr1ᵉ ∘ᵉ map-matching-correspondence-Relaxed-Σ-Decompositionᵉ Dᵉ)
                ( is-inhabited-type-Inhabited-𝔽ᵉ Xᵉ)))
          ( id-equivᵉ))) ∘eᵉ
    ( ( equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-𝔽ᵉ
        (finite-type-Inhabited-𝔽ᵉ Xᵉ))))

is-finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽ᵉ :
  {lᵉ : Level} (Xᵉ : Inhabited-𝔽ᵉ lᵉ) →
  is-finiteᵉ
    ( Σ-Decomposition-Subuniverseᵉ
      ( is-finite-and-inhabited-Propᵉ {lᵉ})
      ( map-compute-Inhabited-𝔽'ᵉ Xᵉ))
is-finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽ᵉ Xᵉ =
  is-finite-equivᵉ
    ( equiv-Σ-Decomposition-Inhabited-𝔽-Σ-Decomposition-𝔽ᵉ Xᵉ)
    ( is-finite-Σ-Decomposition-𝔽ᵉ (finite-type-Inhabited-𝔽ᵉ Xᵉ))

finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽ᵉ :
  {lᵉ : Level} (Xᵉ : Inhabited-𝔽ᵉ lᵉ) → 𝔽ᵉ (lsuc lᵉ)
pr1ᵉ (finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽ᵉ {lᵉ} Xᵉ) =
  Σ-Decomposition-Subuniverseᵉ
    ( is-finite-and-inhabited-Propᵉ {lᵉ})
    ( map-compute-Inhabited-𝔽'ᵉ Xᵉ)
pr2ᵉ (finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽ᵉ Xᵉ) =
  is-finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽ᵉ Xᵉ

module _
  {l1ᵉ l2ᵉ : Level}
  where

  finite-small-cauchy-composition-species-subuniverseᵉ :
    ( Sᵉ Tᵉ : species-Inhabited-𝔽ᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)) (Xᵉ : Inhabited-𝔽ᵉ l1ᵉ) →
    𝔽ᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  finite-small-cauchy-composition-species-subuniverseᵉ Sᵉ Tᵉ Xᵉ =
    Σ-𝔽ᵉ
      ( finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽ᵉ Xᵉ)
      ( λ Dᵉ →
        product-𝔽ᵉ
          ( Sᵉ ( subuniverse-indexing-type-Σ-Decomposition-Subuniverseᵉ
                ( is-finite-and-inhabited-Propᵉ)
                ( map-compute-Inhabited-𝔽'ᵉ Xᵉ)
                ( Dᵉ)))
          ( Π-𝔽ᵉ
            ( finite-type-Inhabited-𝔽ᵉ
              ( map-inv-compute-Inhabited-𝔽'ᵉ
                ( subuniverse-indexing-type-Σ-Decomposition-Subuniverseᵉ
                  ( is-finite-and-inhabited-Propᵉ)
                  ( map-compute-Inhabited-𝔽'ᵉ Xᵉ)
                  ( Dᵉ))))
            ( λ xᵉ →
              Tᵉ ( subuniverse-cotype-Σ-Decomposition-Subuniverseᵉ
                  ( is-finite-and-inhabited-Propᵉ)
                  ( map-compute-Inhabited-𝔽'ᵉ Xᵉ)
                  ( Dᵉ)
                  ( xᵉ)))))

  private
    C1ᵉ :
      ( Sᵉ Tᵉ : species-Inhabited-𝔽ᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)) →
      ( Xᵉ : type-subuniverseᵉ is-finite-and-inhabited-Propᵉ) →
      is-smallᵉ
        (l1ᵉ ⊔ l2ᵉ)
        ( small-cauchy-composition-species-subuniverse'ᵉ
          is-finite-and-inhabited-Propᵉ
          is-finite-Propᵉ
          Sᵉ Tᵉ Xᵉ)
    C1ᵉ Sᵉ Tᵉ Xᵉ =
      is-small-is-finiteᵉ
        (l1ᵉ ⊔ l2ᵉ)
        ( finite-small-cauchy-composition-species-subuniverseᵉ Sᵉ Tᵉ
          (map-inv-compute-Inhabited-𝔽'ᵉ Xᵉ))

    C2ᵉ :
      ( Sᵉ Tᵉ : species-Inhabited-𝔽ᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)) →
      (Xᵉ : type-subuniverseᵉ is-finite-and-inhabited-Propᵉ) →
      is-finiteᵉ (type-is-smallᵉ (C1ᵉ Sᵉ Tᵉ Xᵉ))
    C2ᵉ Sᵉ Tᵉ Xᵉ =
      is-finite-equivᵉ
        ( equiv-is-smallᵉ (C1ᵉ Sᵉ Tᵉ Xᵉ))
        ( is-finite-type-𝔽ᵉ
          ( finite-small-cauchy-composition-species-subuniverseᵉ
            ( Sᵉ)
            ( Tᵉ)
            ( map-inv-compute-Inhabited-𝔽'ᵉ Xᵉ)))

    C3ᵉ : is-closed-under-Σ-subuniverseᵉ (is-finite-and-inhabited-Propᵉ {l1ᵉ})
    C3ᵉ Xᵉ Yᵉ =
      is-finite-Σᵉ
        ( is-finite-Inhabited-𝔽ᵉ (map-inv-compute-Inhabited-𝔽'ᵉ Xᵉ))
        ( λ xᵉ →
          is-finite-Inhabited-𝔽ᵉ (map-inv-compute-Inhabited-𝔽'ᵉ (Yᵉ xᵉ))) ,ᵉ
      is-inhabited-Σᵉ
        ( is-inhabited-type-Inhabited-𝔽ᵉ
          ( map-inv-compute-Inhabited-𝔽'ᵉ Xᵉ))
        ( λ xᵉ → is-inhabited-type-Inhabited-𝔽ᵉ
          ( map-inv-compute-Inhabited-𝔽'ᵉ (Yᵉ xᵉ)))

    C4ᵉ : is-finite-and-inhabitedᵉ (raise-unitᵉ l1ᵉ)
    C4ᵉ =
      is-finite-is-contrᵉ is-contr-raise-unitᵉ ,ᵉ
      is-inhabited-is-contrᵉ is-contr-raise-unitᵉ

    C5ᵉ : (Xᵉ : UUᵉ l1ᵉ) → is-smallᵉ (l1ᵉ ⊔ l2ᵉ) (is-contrᵉ Xᵉ)
    C5ᵉ Xᵉ = is-small-lmaxᵉ l2ᵉ (is-contrᵉ Xᵉ)

    C6ᵉ :
      ( Xᵉ : type-subuniverseᵉ {l1ᵉ} is-finite-and-inhabited-Propᵉ) →
      ( is-finiteᵉ
        ( type-is-smallᵉ
            ( C5ᵉ ( inclusion-subuniverseᵉ is-finite-and-inhabited-Propᵉ Xᵉ))))
    C6ᵉ Xᵉ =
      is-finite-is-decidable-Propᵉ
        ( _ ,ᵉ
          is-prop-equivᵉ
            ( inv-equivᵉ
              ( equiv-is-smallᵉ
                ( is-small-lmaxᵉ l2ᵉ
                  ( is-contrᵉ
                    ( type-Inhabited-𝔽ᵉ
                      ( map-inv-compute-Inhabited-𝔽'ᵉ Xᵉ))))))
                ( is-property-is-contrᵉ))
        ( is-decidable-equivᵉ
          ( inv-equivᵉ
            ( equiv-is-smallᵉ
              ( is-small-lmaxᵉ
                ( l2ᵉ)
                ( is-contrᵉ
                  ( type-Inhabited-𝔽ᵉ
                    ( map-inv-compute-Inhabited-𝔽'ᵉ Xᵉ))))))
          ( is-decidable-is-contr-is-finiteᵉ
            ( is-finite-Inhabited-𝔽ᵉ (map-inv-compute-Inhabited-𝔽'ᵉ Xᵉ))))

  small-cauchy-composition-species-Inhabited-𝔽ᵉ :
    species-Inhabited-𝔽ᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ) →
    species-Inhabited-𝔽ᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ) →
    species-Inhabited-𝔽ᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)
  small-cauchy-composition-species-Inhabited-𝔽ᵉ =
    small-cauchy-composition-species-subuniverseᵉ
      is-finite-and-inhabited-Propᵉ
      is-finite-Propᵉ
      C1ᵉ C2ᵉ C3ᵉ

  small-cauchy-composition-unit-species-Inhabited-𝔽ᵉ :
    species-Inhabited-𝔽ᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)
  small-cauchy-composition-unit-species-Inhabited-𝔽ᵉ =
    small-cauchy-composition-unit-species-subuniverseᵉ
      is-finite-and-inhabited-Propᵉ
      is-finite-Propᵉ
      C1ᵉ C2ᵉ C3ᵉ C4ᵉ C5ᵉ C6ᵉ

  left-unit-law-small-cauchy-composition-species-Inhabited-𝔽ᵉ :
    ( Sᵉ : species-Inhabited-𝔽ᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)) →
    small-cauchy-composition-species-Inhabited-𝔽ᵉ
      small-cauchy-composition-unit-species-Inhabited-𝔽ᵉ
      Sᵉ ＝ᵉ
    Sᵉ
  left-unit-law-small-cauchy-composition-species-Inhabited-𝔽ᵉ =
    left-unit-law-small-cauchy-composition-species-subuniverseᵉ
      is-finite-and-inhabited-Propᵉ
      is-finite-Propᵉ
      C1ᵉ C2ᵉ C3ᵉ C4ᵉ C5ᵉ C6ᵉ

  right-unit-law-small-cauchy-composition-species-Inhabited-𝔽ᵉ :
    ( Sᵉ : species-Inhabited-𝔽ᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)) →
    small-cauchy-composition-species-Inhabited-𝔽ᵉ
      Sᵉ
      small-cauchy-composition-unit-species-Inhabited-𝔽ᵉ ＝ᵉ
    Sᵉ
  right-unit-law-small-cauchy-composition-species-Inhabited-𝔽ᵉ =
    right-unit-law-small-cauchy-composition-species-subuniverseᵉ
      is-finite-and-inhabited-Propᵉ
      is-finite-Propᵉ
      C1ᵉ C2ᵉ C3ᵉ C4ᵉ C5ᵉ C6ᵉ

  associative-small-cauchy-composition-species-Inhabited-𝔽ᵉ :
    (Sᵉ Tᵉ Uᵉ : species-Inhabited-𝔽ᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)) →
    small-cauchy-composition-species-Inhabited-𝔽ᵉ
      ( Sᵉ)
      ( small-cauchy-composition-species-Inhabited-𝔽ᵉ Tᵉ Uᵉ) ＝ᵉ
    small-cauchy-composition-species-Inhabited-𝔽ᵉ
      ( small-cauchy-composition-species-Inhabited-𝔽ᵉ Sᵉ Tᵉ)
      ( Uᵉ)
  associative-small-cauchy-composition-species-Inhabited-𝔽ᵉ =
    associative-small-cauchy-composition-species-subuniverseᵉ
      is-finite-and-inhabited-Propᵉ
      is-finite-Propᵉ
      C1ᵉ C2ᵉ C3ᵉ
```