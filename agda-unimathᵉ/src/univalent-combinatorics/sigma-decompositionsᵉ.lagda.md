# Finite Σ-decompositions of finite types

```agda
module univalent-combinatorics.sigma-decompositionsᵉ where

open import foundation.sigma-decompositionsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.propositionsᵉ
open import foundation.relaxed-sigma-decompositionsᵉ
open import foundation.subtypesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.decidable-equivalence-relationsᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.inhabited-finite-typesᵉ
open import univalent-combinatorics.type-dualityᵉ
```

</details>

## Definition

```agda
Σ-Decomposition-𝔽ᵉ :
  {lᵉ : Level} → (l1ᵉ l2ᵉ : Level) → 𝔽ᵉ lᵉ → UUᵉ (lᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Σ-Decomposition-𝔽ᵉ l1ᵉ l2ᵉ Aᵉ =
  Σᵉ ( 𝔽ᵉ l1ᵉ)
    ( λ Xᵉ →
      Σᵉ ( type-𝔽ᵉ Xᵉ → Inhabited-𝔽ᵉ l2ᵉ)
        ( λ Yᵉ → type-𝔽ᵉ Aᵉ ≃ᵉ (Σᵉ (type-𝔽ᵉ Xᵉ) (λ xᵉ → type-Inhabited-𝔽ᵉ (Yᵉ xᵉ)))))

module _
  {lᵉ l1ᵉ l2ᵉ : Level} (Aᵉ : 𝔽ᵉ lᵉ) (Dᵉ : Σ-Decomposition-𝔽ᵉ l1ᵉ l2ᵉ Aᵉ)
  where

  finite-indexing-type-Σ-Decomposition-𝔽ᵉ : 𝔽ᵉ l1ᵉ
  finite-indexing-type-Σ-Decomposition-𝔽ᵉ = pr1ᵉ Dᵉ

  indexing-type-Σ-Decomposition-𝔽ᵉ : UUᵉ l1ᵉ
  indexing-type-Σ-Decomposition-𝔽ᵉ =
    type-𝔽ᵉ finite-indexing-type-Σ-Decomposition-𝔽ᵉ

  is-finite-indexing-type-Σ-Decomposition-𝔽ᵉ :
    is-finiteᵉ (indexing-type-Σ-Decomposition-𝔽ᵉ)
  is-finite-indexing-type-Σ-Decomposition-𝔽ᵉ =
    is-finite-type-𝔽ᵉ finite-indexing-type-Σ-Decomposition-𝔽ᵉ

  finite-inhabited-cotype-Σ-Decomposition-𝔽ᵉ :
    Fam-Inhabited-Types-𝔽ᵉ l2ᵉ finite-indexing-type-Σ-Decomposition-𝔽ᵉ
  finite-inhabited-cotype-Σ-Decomposition-𝔽ᵉ = pr1ᵉ (pr2ᵉ Dᵉ)

  finite-cotype-Σ-Decomposition-𝔽ᵉ :
    type-𝔽ᵉ finite-indexing-type-Σ-Decomposition-𝔽ᵉ → 𝔽ᵉ l2ᵉ
  finite-cotype-Σ-Decomposition-𝔽ᵉ =
    finite-type-Fam-Inhabited-Types-𝔽ᵉ
      finite-indexing-type-Σ-Decomposition-𝔽ᵉ
      finite-inhabited-cotype-Σ-Decomposition-𝔽ᵉ

  cotype-Σ-Decomposition-𝔽ᵉ :
    type-𝔽ᵉ finite-indexing-type-Σ-Decomposition-𝔽ᵉ → UUᵉ l2ᵉ
  cotype-Σ-Decomposition-𝔽ᵉ xᵉ = type-𝔽ᵉ (finite-cotype-Σ-Decomposition-𝔽ᵉ xᵉ)

  is-finite-cotype-Σ-Decomposition-𝔽ᵉ :
    (xᵉ : type-𝔽ᵉ finite-indexing-type-Σ-Decomposition-𝔽ᵉ) →
    is-finiteᵉ (cotype-Σ-Decomposition-𝔽ᵉ xᵉ)
  is-finite-cotype-Σ-Decomposition-𝔽ᵉ xᵉ =
    is-finite-type-𝔽ᵉ (finite-cotype-Σ-Decomposition-𝔽ᵉ xᵉ)

  is-inhabited-cotype-Σ-Decomposition-𝔽ᵉ :
    (xᵉ : type-𝔽ᵉ finite-indexing-type-Σ-Decomposition-𝔽ᵉ) →
    is-inhabitedᵉ (cotype-Σ-Decomposition-𝔽ᵉ xᵉ)
  is-inhabited-cotype-Σ-Decomposition-𝔽ᵉ xᵉ =
    is-inhabited-type-Inhabited-𝔽ᵉ
      ( finite-inhabited-cotype-Σ-Decomposition-𝔽ᵉ xᵉ)

  inhabited-cotype-Σ-Decomposition-𝔽ᵉ :
    Fam-Inhabited-Typesᵉ l2ᵉ indexing-type-Σ-Decomposition-𝔽ᵉ
  pr1ᵉ (inhabited-cotype-Σ-Decomposition-𝔽ᵉ xᵉ) =
    cotype-Σ-Decomposition-𝔽ᵉ xᵉ
  pr2ᵉ (inhabited-cotype-Σ-Decomposition-𝔽ᵉ xᵉ) =
    is-inhabited-cotype-Σ-Decomposition-𝔽ᵉ xᵉ

  matching-correspondence-Σ-Decomposition-𝔽ᵉ :
    type-𝔽ᵉ Aᵉ ≃ᵉ Σᵉ indexing-type-Σ-Decomposition-𝔽ᵉ cotype-Σ-Decomposition-𝔽ᵉ
  matching-correspondence-Σ-Decomposition-𝔽ᵉ = pr2ᵉ (pr2ᵉ Dᵉ)

  map-matching-correspondence-Σ-Decomposition-𝔽ᵉ :
    type-𝔽ᵉ Aᵉ → Σᵉ indexing-type-Σ-Decomposition-𝔽ᵉ cotype-Σ-Decomposition-𝔽ᵉ
  map-matching-correspondence-Σ-Decomposition-𝔽ᵉ =
    map-equivᵉ matching-correspondence-Σ-Decomposition-𝔽ᵉ

  Σ-Decomposition-Σ-Decomposition-𝔽ᵉ :
    Σ-Decompositionᵉ l1ᵉ l2ᵉ (type-𝔽ᵉ Aᵉ)
  pr1ᵉ Σ-Decomposition-Σ-Decomposition-𝔽ᵉ =
    indexing-type-Σ-Decomposition-𝔽ᵉ
  pr1ᵉ (pr2ᵉ Σ-Decomposition-Σ-Decomposition-𝔽ᵉ) =
    inhabited-cotype-Σ-Decomposition-𝔽ᵉ
  pr2ᵉ (pr2ᵉ Σ-Decomposition-Σ-Decomposition-𝔽ᵉ) =
    matching-correspondence-Σ-Decomposition-𝔽ᵉ
```

### Fibered double finite Σ-decompositions

```agda
fibered-Σ-Decomposition-𝔽ᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level) (Aᵉ : 𝔽ᵉ l1ᵉ) →
  UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ ⊔ lsuc l5ᵉ)
fibered-Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ =
  Σᵉ ( Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ)
    ( λ Dᵉ →
      Σ-Decomposition-𝔽ᵉ l4ᵉ l5ᵉ (finite-indexing-type-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ))
```

### Displayed double Σ-decompositions

```agda
displayed-Σ-Decomposition-𝔽ᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level) (Aᵉ : 𝔽ᵉ l1ᵉ) →
  UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ ⊔ lsuc l5ᵉ)
displayed-Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ =
  ( Σᵉ ( Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ)
      ( λ Dᵉ → (uᵉ : indexing-type-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ) →
        Σ-Decomposition-𝔽ᵉ l4ᵉ l5ᵉ (finite-cotype-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ uᵉ)))
```

## Properties

### Finite Σ-Decomposition as a relaxed Σ-Decomposition with conditions

```agda
equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) →
  Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ ≃ᵉ
  Σᵉ ( Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ (type-𝔽ᵉ Aᵉ))
    ( λ Dᵉ →
      is-finiteᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ) ×ᵉ
      ((xᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ) →
        is-finiteᵉ (cotype-Relaxed-Σ-Decompositionᵉ Dᵉ xᵉ) ×ᵉ
        is-inhabitedᵉ (cotype-Relaxed-Σ-Decompositionᵉ Dᵉ xᵉ)))
pr1ᵉ ( equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-𝔽ᵉ Aᵉ) Dᵉ =
  ( indexing-type-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ ,ᵉ
    ( cotype-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ) ,ᵉ
    ( matching-correspondence-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ)) ,ᵉ
    ( is-finite-indexing-type-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ) ,ᵉ
    ( λ xᵉ → is-finite-cotype-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ xᵉ ,ᵉ
            is-inhabited-cotype-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ xᵉ)
pr2ᵉ ( equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-𝔽ᵉ Aᵉ) =
  is-equiv-is-invertibleᵉ
    ( λ Xᵉ →
      ( pr1ᵉ (pr1ᵉ Xᵉ) ,ᵉ pr1ᵉ (pr2ᵉ Xᵉ)) ,ᵉ
      ( ( λ xᵉ →
          ( pr1ᵉ (pr2ᵉ (pr1ᵉ Xᵉ)) xᵉ ,ᵉ pr1ᵉ (pr2ᵉ (pr2ᵉ Xᵉ) xᵉ)) ,ᵉ
          ( pr2ᵉ (pr2ᵉ (pr2ᵉ Xᵉ) xᵉ))) ,ᵉ
        ( pr2ᵉ (pr2ᵉ (pr1ᵉ Xᵉ)))))
    ( refl-htpyᵉ)
    ( refl-htpyᵉ)
```

### Equivalence between finite surjection and finite Σ-decomposition

```agda
module _
  {lᵉ : Level} (Aᵉ : 𝔽ᵉ lᵉ)
  where

  equiv-finite-surjection-Σ-Decomposition-𝔽ᵉ :
    Σ-Decomposition-𝔽ᵉ lᵉ lᵉ Aᵉ ≃ᵉ Σᵉ (𝔽ᵉ lᵉ) (λ Bᵉ → (type-𝔽ᵉ Aᵉ) ↠ᵉ (type-𝔽ᵉ Bᵉ))
  equiv-finite-surjection-Σ-Decomposition-𝔽ᵉ =
    equiv-Σᵉ
      ( λ Bᵉ → type-𝔽ᵉ Aᵉ ↠ᵉ type-𝔽ᵉ Bᵉ)
      ( id-equivᵉ)
      ( λ Xᵉ → inv-equivᵉ (equiv-surjection-𝔽-family-finite-inhabited-typeᵉ Aᵉ Xᵉ))
```

### Equivalence between finite decidable equivalence relations and finite Σ-decompositions

```agda
  equiv-Decidable-equivalence-relation-𝔽-Σ-Decomposition-𝔽ᵉ :
    Σ-Decomposition-𝔽ᵉ lᵉ lᵉ Aᵉ ≃ᵉ
    Decidable-equivalence-relation-𝔽ᵉ lᵉ Aᵉ
  equiv-Decidable-equivalence-relation-𝔽-Σ-Decomposition-𝔽ᵉ =
    inv-equivᵉ (equiv-Surjection-𝔽-Decidable-equivalence-relation-𝔽ᵉ Aᵉ) ∘eᵉ
    equiv-finite-surjection-Σ-Decomposition-𝔽ᵉ
```

### The type of all finite Σ-Decomposition is finite

```agda
  is-finite-Σ-Decomposition-𝔽ᵉ :
    is-finiteᵉ (Σ-Decomposition-𝔽ᵉ lᵉ lᵉ Aᵉ)
  is-finite-Σ-Decomposition-𝔽ᵉ =
    is-finite-equivᵉ
      ( inv-equivᵉ equiv-Decidable-equivalence-relation-𝔽-Σ-Decomposition-𝔽ᵉ)
      ( is-finite-Decidable-equivalence-relation-𝔽ᵉ Aᵉ)
```

### Characterization of the equality of finite Σ-decompositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ)
  where

  is-finite-Σ-Decompositionᵉ :
    subtypeᵉ (l2ᵉ ⊔ l3ᵉ) (Σ-Decompositionᵉ l2ᵉ l3ᵉ (type-𝔽ᵉ Aᵉ))
  is-finite-Σ-Decompositionᵉ Dᵉ =
    Σ-Propᵉ
      ( is-finite-Propᵉ (indexing-type-Σ-Decompositionᵉ Dᵉ))
      ( λ _ →
        Π-Propᵉ
          ( indexing-type-Σ-Decompositionᵉ Dᵉ)
          ( λ xᵉ → is-finite-Propᵉ (cotype-Σ-Decompositionᵉ Dᵉ xᵉ)))

  map-Σ-Decomposition-𝔽-subtype-is-finiteᵉ :
    type-subtypeᵉ is-finite-Σ-Decompositionᵉ → Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ
  map-Σ-Decomposition-𝔽-subtype-is-finiteᵉ ((Xᵉ ,ᵉ (Yᵉ ,ᵉ eᵉ)) ,ᵉ (fin-Xᵉ ,ᵉ fin-Yᵉ)) =
    ( ( Xᵉ ,ᵉ fin-Xᵉ) ,ᵉ
        ( ( λ xᵉ →
            ( (type-Inhabited-Typeᵉ (Yᵉ xᵉ)) ,ᵉ (fin-Yᵉ xᵉ)) ,ᵉ
              (is-inhabited-type-Inhabited-Typeᵉ (Yᵉ xᵉ))) ,ᵉ
        eᵉ))

  map-inv-Σ-Decomposition-𝔽-subtype-is-finiteᵉ :
    Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ → type-subtypeᵉ is-finite-Σ-Decompositionᵉ
  map-inv-Σ-Decomposition-𝔽-subtype-is-finiteᵉ ((Xᵉ ,ᵉ fin-Xᵉ) ,ᵉ (Yᵉ ,ᵉ eᵉ)) =
    ( ( Xᵉ ,ᵉ
        ( ( λ xᵉ → inhabited-type-Inhabited-𝔽ᵉ (Yᵉ xᵉ)) ,ᵉ
          ( eᵉ))) ,ᵉ
      (fin-Xᵉ ,ᵉ (λ xᵉ → is-finite-Inhabited-𝔽ᵉ (Yᵉ xᵉ))))

  equiv-Σ-Decomposition-𝔽-is-finite-subtypeᵉ :
    type-subtypeᵉ is-finite-Σ-Decompositionᵉ ≃ᵉ Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ
  pr1ᵉ (equiv-Σ-Decomposition-𝔽-is-finite-subtypeᵉ) =
    map-Σ-Decomposition-𝔽-subtype-is-finiteᵉ
  pr2ᵉ (equiv-Σ-Decomposition-𝔽-is-finite-subtypeᵉ) =
    is-equiv-is-invertibleᵉ
      map-inv-Σ-Decomposition-𝔽-subtype-is-finiteᵉ
      refl-htpyᵉ
      refl-htpyᵉ

  is-emb-Σ-Decomposition-Σ-Decomposition-𝔽ᵉ :
    is-embᵉ (Σ-Decomposition-Σ-Decomposition-𝔽ᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} Aᵉ)
  is-emb-Σ-Decomposition-Σ-Decomposition-𝔽ᵉ =
    is-emb-triangle-is-equivᵉ
      ( Σ-Decomposition-Σ-Decomposition-𝔽ᵉ Aᵉ)
      ( pr1ᵉ)
      ( map-inv-equivᵉ ( equiv-Σ-Decomposition-𝔽-is-finite-subtypeᵉ))
      ( refl-htpyᵉ)
      ( is-equiv-map-inv-equivᵉ
        ( equiv-Σ-Decomposition-𝔽-is-finite-subtypeᵉ))
      ( is-emb-inclusion-subtypeᵉ (is-finite-Σ-Decompositionᵉ))

  emb-Σ-Decomposition-Σ-Decomposition-𝔽ᵉ :
    Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ ↪ᵉ Σ-Decompositionᵉ l2ᵉ l3ᵉ (type-𝔽ᵉ Aᵉ)
  pr1ᵉ (emb-Σ-Decomposition-Σ-Decomposition-𝔽ᵉ) =
    Σ-Decomposition-Σ-Decomposition-𝔽ᵉ Aᵉ
  pr2ᵉ (emb-Σ-Decomposition-Σ-Decomposition-𝔽ᵉ) =
    is-emb-Σ-Decomposition-Σ-Decomposition-𝔽ᵉ

equiv-Σ-Decomposition-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ)
  (Xᵉ : Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ) (Yᵉ : Σ-Decomposition-𝔽ᵉ l4ᵉ l5ᵉ Aᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
equiv-Σ-Decomposition-𝔽ᵉ Aᵉ Xᵉ Yᵉ =
  equiv-Σ-Decompositionᵉ
    ( Σ-Decomposition-Σ-Decomposition-𝔽ᵉ Aᵉ Xᵉ)
    ( Σ-Decomposition-Σ-Decomposition-𝔽ᵉ Aᵉ Yᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ)
  (Xᵉ : Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ) (Yᵉ : Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  extensionality-Σ-Decomposition-𝔽ᵉ :
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-Σ-Decomposition-𝔽ᵉ Aᵉ Xᵉ Yᵉ
  extensionality-Σ-Decomposition-𝔽ᵉ =
    extensionality-Σ-Decompositionᵉ
      ( Σ-Decomposition-Σ-Decomposition-𝔽ᵉ Aᵉ Xᵉ)
      ( Σ-Decomposition-Σ-Decomposition-𝔽ᵉ Aᵉ Yᵉ) ∘eᵉ
    equiv-ap-embᵉ (emb-Σ-Decomposition-Σ-Decomposition-𝔽ᵉ Aᵉ)

  eq-equiv-Σ-Decomposition-𝔽ᵉ :
    equiv-Σ-Decomposition-𝔽ᵉ Aᵉ Xᵉ Yᵉ → (Xᵉ ＝ᵉ Yᵉ)
  eq-equiv-Σ-Decomposition-𝔽ᵉ =
    map-inv-equivᵉ (extensionality-Σ-Decomposition-𝔽ᵉ)
```

### Iterated finite Σ-Decomposition

#### Fibered finite Σ-Decomposition as a subtype

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ)
  where

  is-finite-fibered-Σ-Decompositionᵉ :
    subtypeᵉ (l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
      ( fibered-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ (type-𝔽ᵉ Aᵉ))
  is-finite-fibered-Σ-Decompositionᵉ Dᵉ =
    Σ-Propᵉ
      ( is-finite-Σ-Decompositionᵉ Aᵉ ( fst-fibered-Σ-Decompositionᵉ Dᵉ))
      ( λ pᵉ →
        is-finite-Σ-Decompositionᵉ
          ( indexing-type-fst-fibered-Σ-Decompositionᵉ Dᵉ ,ᵉ
            (pr1ᵉ pᵉ))
          ( snd-fibered-Σ-Decompositionᵉ Dᵉ))

  equiv-fibered-Σ-Decomposition-𝔽-is-finite-subtypeᵉ :
    type-subtypeᵉ is-finite-fibered-Σ-Decompositionᵉ ≃ᵉ
    fibered-Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ
  equiv-fibered-Σ-Decomposition-𝔽-is-finite-subtypeᵉ =
    equiv-Σᵉ
      ( λ Dᵉ →
        Σ-Decomposition-𝔽ᵉ l4ᵉ l5ᵉ ( finite-indexing-type-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ))
      ( equiv-Σ-Decomposition-𝔽-is-finite-subtypeᵉ Aᵉ)
      ( λ xᵉ →
        equiv-Σ-Decomposition-𝔽-is-finite-subtypeᵉ
        ( indexing-type-Σ-Decompositionᵉ
          ( inclusion-subtypeᵉ (is-finite-Σ-Decompositionᵉ Aᵉ) xᵉ) ,ᵉ
            pr1ᵉ
              ( is-in-subtype-inclusion-subtypeᵉ
                ( is-finite-Σ-Decompositionᵉ Aᵉ)
                (xᵉ)))) ∘eᵉ
      interchange-Σ-Σᵉ
        ( λ Dᵉ D'ᵉ pᵉ →
          type-Propᵉ
            ( is-finite-Σ-Decompositionᵉ
              ( indexing-type-Σ-Decompositionᵉ Dᵉ ,ᵉ
                pr1ᵉ pᵉ)
              ( D'ᵉ)))
```

#### Displayed finite Σ-Decomposition as a subtype

```agda
  is-finite-displayed-Σ-Decompositionᵉ :
    subtypeᵉ (l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
      ( displayed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ (type-𝔽ᵉ Aᵉ))
  is-finite-displayed-Σ-Decompositionᵉ Dᵉ =
    Σ-Propᵉ
      ( is-finite-Σ-Decompositionᵉ Aᵉ (fst-displayed-Σ-Decompositionᵉ Dᵉ))
      ( λ pᵉ →
        Π-Propᵉ
          ( indexing-type-fst-displayed-Σ-Decompositionᵉ Dᵉ)
          ( λ xᵉ →
            is-finite-Σ-Decompositionᵉ
              ( cotype-fst-displayed-Σ-Decompositionᵉ Dᵉ xᵉ ,ᵉ
                pr2ᵉ pᵉ xᵉ)
              ( snd-displayed-Σ-Decompositionᵉ Dᵉ xᵉ)))

  equiv-displayed-Σ-Decomposition-𝔽-is-finite-subtypeᵉ :
    type-subtypeᵉ is-finite-displayed-Σ-Decompositionᵉ ≃ᵉ
    displayed-Σ-Decomposition-𝔽ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ
  equiv-displayed-Σ-Decomposition-𝔽-is-finite-subtypeᵉ =
    equiv-Σᵉ
      ( λ Dᵉ →
        ( xᵉ : indexing-type-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ) →
        ( Σ-Decomposition-𝔽ᵉ l4ᵉ l5ᵉ ( finite-cotype-Σ-Decomposition-𝔽ᵉ Aᵉ Dᵉ xᵉ)))
      ( equiv-Σ-Decomposition-𝔽-is-finite-subtypeᵉ Aᵉ)
      ( λ D1ᵉ →
        equiv-Πᵉ
          ( _)
          ( id-equivᵉ)
          ( λ xᵉ →
            equiv-Σ-Decomposition-𝔽-is-finite-subtypeᵉ
            ( ( cotype-Σ-Decompositionᵉ
                ( inclusion-subtypeᵉ (is-finite-Σ-Decompositionᵉ Aᵉ) D1ᵉ)
                ( xᵉ)) ,ᵉ
              pr2ᵉ
                ( is-in-subtype-inclusion-subtypeᵉ
                  ( is-finite-Σ-Decompositionᵉ Aᵉ) D1ᵉ) xᵉ)) ∘eᵉ
          inv-distributive-Π-Σᵉ) ∘eᵉ
      interchange-Σ-Σᵉ _
```

#### Fibered finite Σ-decompositions and displayed finite Σ-Decomposition are equivalent

```agda
module _
  {l1ᵉ lᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ)
  (Dᵉ : fibered-Σ-Decompositionᵉ lᵉ lᵉ lᵉ lᵉ (type-𝔽ᵉ Aᵉ))
  where

  map-is-finite-displayed-fibered-Σ-Decompositionᵉ :
    type-Propᵉ (is-finite-fibered-Σ-Decompositionᵉ Aᵉ Dᵉ) →
    type-Propᵉ (is-finite-displayed-Σ-Decompositionᵉ Aᵉ
      (map-equivᵉ equiv-displayed-fibered-Σ-Decompositionᵉ Dᵉ))
  pr1ᵉ (pr1ᵉ (map-is-finite-displayed-fibered-Σ-Decompositionᵉ pᵉ)) =
    pr1ᵉ (pr2ᵉ pᵉ)
  pr2ᵉ (pr1ᵉ (map-is-finite-displayed-fibered-Σ-Decompositionᵉ pᵉ)) =
    λ uᵉ → is-finite-Σᵉ (pr2ᵉ (pr2ᵉ pᵉ) uᵉ) (λ vᵉ → (pr2ᵉ (pr1ᵉ pᵉ)) _)
  pr1ᵉ (pr2ᵉ (map-is-finite-displayed-fibered-Σ-Decompositionᵉ pᵉ) uᵉ) =
    pr2ᵉ (pr2ᵉ pᵉ) uᵉ
  pr2ᵉ (pr2ᵉ (map-is-finite-displayed-fibered-Σ-Decompositionᵉ pᵉ) uᵉ) =
    λ vᵉ → (pr2ᵉ (pr1ᵉ pᵉ)) _

  map-inv-is-finite-displayed-fibered-Σ-Decompositionᵉ :
    type-Propᵉ (is-finite-displayed-Σ-Decompositionᵉ Aᵉ
      (map-equivᵉ equiv-displayed-fibered-Σ-Decompositionᵉ Dᵉ)) →
    type-Propᵉ (is-finite-fibered-Σ-Decompositionᵉ Aᵉ Dᵉ)
  pr1ᵉ (pr1ᵉ (map-inv-is-finite-displayed-fibered-Σ-Decompositionᵉ pᵉ)) =
    is-finite-equivᵉ
      ( inv-equivᵉ (matching-correspondence-snd-fibered-Σ-Decompositionᵉ Dᵉ))
      ( is-finite-Σᵉ (pr1ᵉ (pr1ᵉ pᵉ)) λ uᵉ → (pr1ᵉ (pr2ᵉ pᵉ uᵉ)))
  pr2ᵉ (pr1ᵉ (map-inv-is-finite-displayed-fibered-Σ-Decompositionᵉ pᵉ)) =
    map-inv-equivᵉ
      ( equiv-precomp-Πᵉ
        ( inv-equivᵉ ( matching-correspondence-snd-fibered-Σ-Decompositionᵉ Dᵉ))
        ( λ zᵉ → is-finiteᵉ (cotype-fst-fibered-Σ-Decompositionᵉ Dᵉ zᵉ)))
      λ uvᵉ → pr2ᵉ (pr2ᵉ pᵉ (pr1ᵉ uvᵉ)) (pr2ᵉ uvᵉ)
  pr1ᵉ (pr2ᵉ (map-inv-is-finite-displayed-fibered-Σ-Decompositionᵉ pᵉ)) =
    pr1ᵉ (pr1ᵉ pᵉ)
  pr2ᵉ (pr2ᵉ (map-inv-is-finite-displayed-fibered-Σ-Decompositionᵉ pᵉ)) =
    λ uᵉ → pr1ᵉ (pr2ᵉ pᵉ uᵉ)

  equiv-is-finite-displayed-fibered-Σ-Decompositionᵉ :
    type-Propᵉ (is-finite-fibered-Σ-Decompositionᵉ Aᵉ Dᵉ) ≃ᵉ
    type-Propᵉ (is-finite-displayed-Σ-Decompositionᵉ Aᵉ
      (map-equivᵉ equiv-displayed-fibered-Σ-Decompositionᵉ Dᵉ))
  equiv-is-finite-displayed-fibered-Σ-Decompositionᵉ =
    equiv-iff-is-propᵉ
      ( is-prop-type-Propᵉ (is-finite-fibered-Σ-Decompositionᵉ Aᵉ Dᵉ))
      ( is-prop-type-Propᵉ
        ( is-finite-displayed-Σ-Decompositionᵉ Aᵉ
          ( map-equivᵉ equiv-displayed-fibered-Σ-Decompositionᵉ Dᵉ)))
      ( map-is-finite-displayed-fibered-Σ-Decompositionᵉ)
      ( map-inv-is-finite-displayed-fibered-Σ-Decompositionᵉ)

equiv-displayed-fibered-Σ-Decomposition-𝔽ᵉ :
  {l1ᵉ lᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) →
  fibered-Σ-Decomposition-𝔽ᵉ lᵉ lᵉ lᵉ lᵉ Aᵉ ≃ᵉ displayed-Σ-Decomposition-𝔽ᵉ lᵉ lᵉ lᵉ lᵉ Aᵉ
equiv-displayed-fibered-Σ-Decomposition-𝔽ᵉ Aᵉ =
  equiv-displayed-Σ-Decomposition-𝔽-is-finite-subtypeᵉ Aᵉ ∘eᵉ
    ( equiv-Σᵉ
        ( λ xᵉ → type-Propᵉ (is-finite-displayed-Σ-Decompositionᵉ Aᵉ xᵉ))
        ( equiv-displayed-fibered-Σ-Decompositionᵉ)
        ( equiv-is-finite-displayed-fibered-Σ-Decompositionᵉ Aᵉ) ∘eᵉ
      inv-equivᵉ ( equiv-fibered-Σ-Decomposition-𝔽-is-finite-subtypeᵉ Aᵉ))
```