# Iterated cartesian product types

```agda
module foundation.iterated-cartesian-product-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.permutations-standard-finite-typesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-function-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universal-property-empty-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ

open import lists.arraysᵉ
open import lists.concatenation-listsᵉ
open import lists.listsᵉ
open import lists.permutation-listsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Inᵉ thisᵉ file,ᵉ weᵉ giveᵉ threeᵉ definitionsᵉ ofᵉ theᵉ iteratedᵉ cartesianᵉ productᵉ
`A₁ᵉ ×ᵉ ... ×ᵉ Aₙ`ᵉ ofᵉ `n`ᵉ typesᵉ `A₁ᵉ ,ᵉ ... ,ᵉ Aₙ`.ᵉ Twoᵉ useᵉ aᵉ familyᵉ ofᵉ typesᵉ overᵉ
`Finᵉ n`ᵉ: theᵉ firstᵉ usesᵉ recursionᵉ overᵉ `Finᵉ n`ᵉ andᵉ theᵉ secondᵉ isᵉ justᵉ
`Πᵉ (Finᵉ nᵉ) A`.ᵉ Theᵉ lastᵉ oneᵉ usesᵉ lists.ᵉ

Weᵉ showᵉ thatᵉ :

-ᵉ allᵉ ofᵉ theseᵉ definitionsᵉ areᵉ equivalentᵉ
-ᵉ iteratedᵉ cartesianᵉ productᵉ ofᵉ typesᵉ isᵉ closedᵉ underᵉ permutationsᵉ

## Definitions

### Via a family of types over `Fin n`

#### Using recursion

```agda
iterated-product-Fin-recursiveᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) →
  ((Finᵉ nᵉ) → UUᵉ lᵉ) → UUᵉ lᵉ
iterated-product-Fin-recursiveᵉ {lᵉ} zero-ℕᵉ Aᵉ = raise-unitᵉ lᵉ
iterated-product-Fin-recursiveᵉ (succ-ℕᵉ nᵉ) Aᵉ =
  Aᵉ (inrᵉ starᵉ) ×ᵉ iterated-product-Fin-recursiveᵉ nᵉ (Aᵉ ∘ᵉ inlᵉ)
```

#### Using `Π`-types

```agda
iterated-product-Fin-Πᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) →
  ((Finᵉ nᵉ) → UUᵉ lᵉ) → UUᵉ lᵉ
iterated-product-Fin-Πᵉ nᵉ Aᵉ = (iᵉ : Finᵉ nᵉ) → Aᵉ iᵉ
```

### Via lists

```agda
iterated-product-listsᵉ :
  {lᵉ : Level} → listᵉ (UUᵉ lᵉ) → UUᵉ lᵉ
iterated-product-listsᵉ {lᵉ} nilᵉ = raise-unitᵉ lᵉ
iterated-product-listsᵉ (consᵉ Aᵉ pᵉ) = Aᵉ ×ᵉ iterated-product-listsᵉ pᵉ
```

## Properties

### The definitions using recursion and `Π`-types are equivalent

```agda
equiv-iterated-product-Fin-recursive-Πᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : (Finᵉ nᵉ → UUᵉ lᵉ)) →
  iterated-product-Fin-recursiveᵉ nᵉ Aᵉ ≃ᵉ
  iterated-product-Fin-Πᵉ nᵉ Aᵉ
equiv-iterated-product-Fin-recursive-Πᵉ zero-ℕᵉ Aᵉ =
  equiv-is-contrᵉ is-contr-raise-unitᵉ (dependent-universal-property-empty'ᵉ Aᵉ)
equiv-iterated-product-Fin-recursive-Πᵉ (succ-ℕᵉ nᵉ) Aᵉ =
  ( ( inv-equivᵉ (equiv-dependent-universal-property-coproductᵉ Aᵉ)) ∘eᵉ
    ( ( commutative-productᵉ) ∘eᵉ
      ( ( equiv-productᵉ
            ( inv-equivᵉ (left-unit-law-Π-is-contrᵉ is-contr-unitᵉ starᵉ))
            ( id-equivᵉ)) ∘eᵉ
        ( ( equiv-productᵉ
              ( id-equivᵉ)
              ( equiv-iterated-product-Fin-recursive-Πᵉ nᵉ (Aᵉ ∘ᵉ inlᵉ)))))))
```

### The definitions using recursion and lists are equivalent

```agda
equiv-iterated-product-Fin-recursive-listsᵉ :
  {lᵉ : Level} (lᵉ : listᵉ (UUᵉ lᵉ)) →
  iterated-product-Fin-recursiveᵉ
    ( length-arrayᵉ (array-listᵉ lᵉ))
    ( functional-vec-arrayᵉ (array-listᵉ lᵉ)) ≃ᵉ
  iterated-product-listsᵉ lᵉ
equiv-iterated-product-Fin-recursive-listsᵉ nilᵉ = id-equivᵉ
equiv-iterated-product-Fin-recursive-listsᵉ (consᵉ xᵉ lᵉ) =
  equiv-productᵉ id-equivᵉ (equiv-iterated-product-Fin-recursive-listsᵉ lᵉ)
```

### The cartesian product of two iterated cartesian products (via list) is the iterated cartesian product of the concatenation of the corresponding lists

```agda
equiv-product-iterated-product-listsᵉ :
  {lᵉ : Level} (pᵉ qᵉ : listᵉ (UUᵉ lᵉ)) →
  (iterated-product-listsᵉ pᵉ ×ᵉ iterated-product-listsᵉ qᵉ) ≃ᵉ
  iterated-product-listsᵉ (concat-listᵉ pᵉ qᵉ)
equiv-product-iterated-product-listsᵉ nilᵉ qᵉ =
  left-unit-law-product-is-contrᵉ (is-contr-raise-unitᵉ)
equiv-product-iterated-product-listsᵉ (consᵉ xᵉ pᵉ) qᵉ =
  ( ( equiv-productᵉ
      ( id-equivᵉ)
      ( equiv-product-iterated-product-listsᵉ pᵉ qᵉ)) ∘eᵉ
    ( associative-productᵉ
      ( xᵉ)
      ( iterated-product-listsᵉ pᵉ)
      ( iterated-product-listsᵉ qᵉ)))
```

### Iterated cartesian product is closed under permutations

```agda
permutation-iterated-product-Fin-Πᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : (Finᵉ nᵉ → UUᵉ lᵉ)) (tᵉ : Permutationᵉ nᵉ) → UUᵉ lᵉ
permutation-iterated-product-Fin-Πᵉ nᵉ Aᵉ tᵉ =
  iterated-product-Fin-Πᵉ nᵉ (Aᵉ ∘ᵉ map-equivᵉ tᵉ)

equiv-permutation-iterated-product-Fin-Πᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : (Finᵉ nᵉ → UUᵉ lᵉ)) (tᵉ : Permutationᵉ nᵉ) →
  permutation-iterated-product-Fin-Πᵉ nᵉ Aᵉ tᵉ ≃ᵉ iterated-product-Fin-Πᵉ nᵉ Aᵉ
equiv-permutation-iterated-product-Fin-Πᵉ nᵉ Aᵉ tᵉ =
  equiv-Πᵉ (λ zᵉ → Aᵉ zᵉ) tᵉ (λ aᵉ → id-equivᵉ)

eq-permutation-iterated-product-Fin-Πᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : (Finᵉ nᵉ → UUᵉ lᵉ)) (tᵉ : Permutationᵉ nᵉ) →
  permutation-iterated-product-Fin-Πᵉ nᵉ Aᵉ tᵉ ＝ᵉ iterated-product-Fin-Πᵉ nᵉ Aᵉ
eq-permutation-iterated-product-Fin-Πᵉ nᵉ Aᵉ tᵉ =
  eq-equivᵉ (equiv-permutation-iterated-product-Fin-Πᵉ nᵉ Aᵉ tᵉ)

permutation-iterated-product-Fin-recursiveᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : (Finᵉ nᵉ → UUᵉ lᵉ)) (tᵉ : Permutationᵉ nᵉ) → UUᵉ lᵉ
permutation-iterated-product-Fin-recursiveᵉ nᵉ Aᵉ tᵉ =
  iterated-product-Fin-recursiveᵉ nᵉ (Aᵉ ∘ᵉ map-equivᵉ tᵉ)

equiv-permutation-iterated-product-Fin-recursiveᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : (Finᵉ nᵉ → UUᵉ lᵉ)) (tᵉ : Permutationᵉ nᵉ) →
  permutation-iterated-product-Fin-recursiveᵉ nᵉ Aᵉ tᵉ ≃ᵉ
  iterated-product-Fin-recursiveᵉ nᵉ Aᵉ
equiv-permutation-iterated-product-Fin-recursiveᵉ nᵉ Aᵉ tᵉ =
  ( inv-equivᵉ (equiv-iterated-product-Fin-recursive-Πᵉ nᵉ Aᵉ)) ∘eᵉ
  ( equiv-permutation-iterated-product-Fin-Πᵉ nᵉ Aᵉ tᵉ) ∘eᵉ
  ( equiv-iterated-product-Fin-recursive-Πᵉ nᵉ (Aᵉ ∘ᵉ map-equivᵉ tᵉ))

eq-permutation-iterated-product-Fin-recursiveᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : (Finᵉ nᵉ → UUᵉ lᵉ)) (tᵉ : Permutationᵉ nᵉ) →
  permutation-iterated-product-Fin-recursiveᵉ nᵉ Aᵉ tᵉ ＝ᵉ
  iterated-product-Fin-recursiveᵉ nᵉ Aᵉ
eq-permutation-iterated-product-Fin-recursiveᵉ nᵉ Aᵉ tᵉ =
  eq-equivᵉ (equiv-permutation-iterated-product-Fin-recursiveᵉ nᵉ Aᵉ tᵉ)

permutation-iterated-product-listsᵉ :
  {lᵉ : Level} (Lᵉ : listᵉ (UUᵉ lᵉ)) (tᵉ : Permutationᵉ (length-listᵉ Lᵉ)) → UUᵉ lᵉ
permutation-iterated-product-listsᵉ Lᵉ tᵉ =
  iterated-product-listsᵉ (permute-listᵉ Lᵉ tᵉ)

equiv-permutation-iterated-product-listsᵉ :
  {lᵉ : Level} (Lᵉ : listᵉ (UUᵉ lᵉ)) (tᵉ : Permutationᵉ (length-listᵉ Lᵉ)) →
  permutation-iterated-product-listsᵉ Lᵉ tᵉ ≃ᵉ
  iterated-product-listsᵉ Lᵉ
equiv-permutation-iterated-product-listsᵉ Lᵉ tᵉ =
  ( equiv-iterated-product-Fin-recursive-listsᵉ Lᵉ ∘eᵉ
    ( ( equiv-permutation-iterated-product-Fin-recursiveᵉ
        ( length-listᵉ Lᵉ)
        ( functional-vec-arrayᵉ (array-listᵉ Lᵉ))
        ( tᵉ)) ∘eᵉ
      ( equiv-eqᵉ
        ( apᵉ
          ( λ pᵉ →
            iterated-product-Fin-recursiveᵉ
              ( length-arrayᵉ pᵉ)
              ( functional-vec-arrayᵉ pᵉ))
          ( is-retraction-array-listᵉ
            ( length-listᵉ Lᵉ ,ᵉ
              ( functional-vec-arrayᵉ (array-listᵉ Lᵉ) ∘ᵉ map-equivᵉ tᵉ)))) ∘eᵉ
        ( inv-equivᵉ
          ( equiv-iterated-product-Fin-recursive-listsᵉ (permute-listᵉ Lᵉ tᵉ))))))

eq-permutation-iterated-product-listsᵉ :
  {lᵉ : Level} (Lᵉ : listᵉ (UUᵉ lᵉ)) (tᵉ : Permutationᵉ (length-listᵉ Lᵉ)) →
  permutation-iterated-product-listsᵉ Lᵉ tᵉ ＝ᵉ
  iterated-product-listsᵉ Lᵉ
eq-permutation-iterated-product-listsᵉ Lᵉ tᵉ =
  eq-equivᵉ (equiv-permutation-iterated-product-listsᵉ Lᵉ tᵉ)
```