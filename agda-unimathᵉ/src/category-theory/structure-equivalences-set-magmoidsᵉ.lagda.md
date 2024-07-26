# Structure equivalences between set-magmoids

```agda
module category-theory.structure-equivalences-set-magmoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-set-magmoidsᵉ
open import category-theory.set-magmoidsᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **structureᵉ equivalenceᵉ betweenᵉ
[set-magmoids](category-theory.set-magmoids.md)**ᵉ isᵉ aᵉ
[functor](category-theory.functors-set-magmoids.mdᵉ) thatᵉ isᵉ

1.ᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) onᵉ objects,ᵉ andᵉ
2.ᵉ anᵉ equivalenceᵉ onᵉ hom-[sets](foundation-core.sets.md),ᵉ i.e.ᵉ isᵉ fullyᵉ
   faithful.ᵉ

## Definitions

### The predicate on functors of set-magmoids of being structure equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) (Bᵉ : Set-Magmoidᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Set-Magmoidᵉ Aᵉ Bᵉ)
  where

  is-structure-equiv-functor-Set-Magmoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-structure-equiv-functor-Set-Magmoidᵉ =
    ( is-equivᵉ (obj-functor-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ)) ×ᵉ
    ( {xᵉ yᵉ : obj-Set-Magmoidᵉ Aᵉ} →
      is-equivᵉ (hom-functor-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ {xᵉ} {yᵉ}))

  is-prop-is-structure-equiv-functor-Set-Magmoidᵉ :
    is-propᵉ is-structure-equiv-functor-Set-Magmoidᵉ
  is-prop-is-structure-equiv-functor-Set-Magmoidᵉ =
    is-prop-productᵉ
      ( is-property-is-equivᵉ (obj-functor-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ))
      ( is-prop-iterated-implicit-Πᵉ 2
        ( λ xᵉ yᵉ → is-property-is-equivᵉ (hom-functor-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ {xᵉ} {yᵉ})))

  is-equiv-prop-functor-Set-Magmoidᵉ :
    Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-equiv-prop-functor-Set-Magmoidᵉ =
    is-structure-equiv-functor-Set-Magmoidᵉ
  pr2ᵉ is-equiv-prop-functor-Set-Magmoidᵉ =
    is-prop-is-structure-equiv-functor-Set-Magmoidᵉ
```

### The type of structure equivalences between set-magmoids

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) (Bᵉ : Set-Magmoidᵉ l3ᵉ l4ᵉ)
  where

  structure-equiv-Set-Magmoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  structure-equiv-Set-Magmoidᵉ =
    Σᵉ ( functor-Set-Magmoidᵉ Aᵉ Bᵉ)
      ( is-structure-equiv-functor-Set-Magmoidᵉ Aᵉ Bᵉ)
```

### The identity structure equivalence on a set-magmoid

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ)
  where

  is-equiv-id-Set-Magmoidᵉ :
    is-structure-equiv-functor-Set-Magmoidᵉ Aᵉ Aᵉ (id-functor-Set-Magmoidᵉ Aᵉ)
  pr1ᵉ is-equiv-id-Set-Magmoidᵉ = is-equiv-idᵉ
  pr2ᵉ is-equiv-id-Set-Magmoidᵉ = is-equiv-idᵉ

  id-structure-equiv-Set-Magmoidᵉ : structure-equiv-Set-Magmoidᵉ Aᵉ Aᵉ
  pr1ᵉ id-structure-equiv-Set-Magmoidᵉ = id-functor-Set-Magmoidᵉ Aᵉ
  pr2ᵉ id-structure-equiv-Set-Magmoidᵉ = is-equiv-id-Set-Magmoidᵉ
```

## Properties

### Computing the type of structure equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) (Bᵉ : Set-Magmoidᵉ l3ᵉ l4ᵉ)
  where

  componentwise-structure-equiv-Set-Magmoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  componentwise-structure-equiv-Set-Magmoidᵉ =
    Σᵉ ( obj-Set-Magmoidᵉ Aᵉ ≃ᵉ obj-Set-Magmoidᵉ Bᵉ)
      ( λ E₀ᵉ →
        Σᵉ ( {xᵉ yᵉ : obj-Set-Magmoidᵉ Aᵉ} →
            hom-Set-Magmoidᵉ Aᵉ xᵉ yᵉ ≃ᵉ
            hom-Set-Magmoidᵉ Bᵉ (map-equivᵉ E₀ᵉ xᵉ) (map-equivᵉ E₀ᵉ yᵉ))
          ( λ E₁ᵉ →
            preserves-comp-hom-Set-Magmoidᵉ Aᵉ Bᵉ
              ( map-equivᵉ E₀ᵉ) (map-equivᵉ E₁ᵉ)))

  compute-structure-equiv-Set-Magmoidᵉ :
    componentwise-structure-equiv-Set-Magmoidᵉ ≃ᵉ structure-equiv-Set-Magmoidᵉ Aᵉ Bᵉ
  compute-structure-equiv-Set-Magmoidᵉ =
    ( inv-associative-Σᵉ _ _ _) ∘eᵉ
    ( equiv-totᵉ
      ( λ F₀ᵉ →
        ( inv-associative-Σᵉ _ _ _) ∘eᵉ
        equiv-totᵉ (λ _ → equiv-left-swap-Σᵉ) ∘eᵉ
        ( equiv-left-swap-Σᵉ) ∘eᵉ
        ( equiv-totᵉ
          ( λ is-equiv-F₀ᵉ →
            ( associative-Σᵉ _ _ _) ∘eᵉ
            ( equiv-right-swap-Σᵉ) ∘eᵉ
            ( equiv-Σ-equiv-baseᵉ
              ( λ E₁'ᵉ →
                preserves-comp-hom-Set-Magmoidᵉ Aᵉ Bᵉ F₀ᵉ (λ fᵉ → pr1ᵉ E₁'ᵉ fᵉ))
              ( ( distributive-implicit-Π-Σᵉ) ∘eᵉ
                ( equiv-implicit-Π-equiv-familyᵉ
                  ( λ _ → distributive-implicit-Π-Σᵉ)))))))) ∘eᵉ
    ( associative-Σᵉ _ _ _)
```

### Structure equivalences of set-magmoids characterize their equality

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  where

  structure-equiv-eq-Set-Magmoidᵉ :
    (Aᵉ Bᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) →
    Aᵉ ＝ᵉ Bᵉ → structure-equiv-Set-Magmoidᵉ Aᵉ Bᵉ
  structure-equiv-eq-Set-Magmoidᵉ Aᵉ .Aᵉ reflᵉ =
    id-structure-equiv-Set-Magmoidᵉ Aᵉ
```

Theᵉ restᵉ remainsᵉ to beᵉ figuredᵉ out.ᵉ Weᵉ needᵉ theᵉ factᵉ thatᵉ binaryᵉ familiesᵉ ofᵉ
equivalencesᵉ ofᵉ setsᵉ areᵉ torsorial.ᵉ

```text
  is-torsorial-structure-equiv-Set-Magmoidᵉ :
    (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) → is-torsorialᵉ (structure-equiv-Set-Magmoidᵉ Aᵉ)
  is-torsorial-structure-equiv-Set-Magmoidᵉ Aᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (Set-Magmoidᵉ l1ᵉ l2ᵉ) (componentwise-structure-equiv-Set-Magmoidᵉ Aᵉ))
      (equiv-totᵉ (compute-structure-equiv-Set-Magmoidᵉ Aᵉ))
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-equivᵉ (obj-Set-Magmoidᵉ Aᵉ))
        ( obj-Set-Magmoidᵉ Aᵉ ,ᵉ id-equivᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( {!ᵉ   !ᵉ})
          ( hom-set-Set-Magmoidᵉ Aᵉ ,ᵉ λ {xᵉ} {yᵉ} → id-equivᵉ)
          ( is-torsorial-Eq-implicit-Πᵉ
            λ xᵉ → is-torsorial-Eq-implicit-Πᵉ
              λ yᵉ → is-torsorial-Eq-implicit-Πᵉ
                λ zᵉ → {!ᵉ  zᵉ !ᵉ})))
```