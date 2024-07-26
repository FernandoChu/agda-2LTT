# Permutations of lists

```agda
module lists.permutation-listsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.permutations-standard-finite-typesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.functoriality-vectorsᵉ
open import linear-algebra.vectorsᵉ

open import lists.arraysᵉ
open import lists.functoriality-listsᵉ
open import lists.listsᵉ
open import lists.permutation-vectorsᵉ
```

</details>

## Idea

Givenᵉ anᵉ arrayᵉ `t`ᵉ ofᵉ lengthᵉ `n`ᵉ andᵉ aᵉ automorphismᵉ `σ`ᵉ ofᵉ `Finᵉ n`,ᵉ theᵉ
permutationᵉ ofᵉ `t`ᵉ accordingᵉ to `σ`ᵉ isᵉ theᵉ arrayᵉ where theᵉ indexᵉ areᵉ permutedᵉ byᵉ
`σ`.ᵉ Then,ᵉ weᵉ canᵉ defineᵉ whatᵉ isᵉ aᵉ permutationᵉ ofᵉ aᵉ listᵉ ofᵉ lengthᵉ `n`ᵉ viaᵉ theᵉ
equivalenceᵉ betweenᵉ arraysᵉ andᵉ lists.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  permute-listᵉ : (lᵉ : listᵉ Aᵉ) → Permutationᵉ (length-listᵉ lᵉ) → listᵉ Aᵉ
  permute-listᵉ lᵉ sᵉ =
    list-vecᵉ
      ( length-listᵉ lᵉ)
      ( permute-vecᵉ (length-listᵉ lᵉ) (vec-listᵉ lᵉ) sᵉ)
```

### The predicate that a function from `list` to `list` is permuting lists

```agda
  is-permutation-listᵉ : (listᵉ Aᵉ → listᵉ Aᵉ) → UUᵉ lᵉ
  is-permutation-listᵉ fᵉ =
    (lᵉ : listᵉ Aᵉ) →
    Σᵉ ( Permutationᵉ (length-listᵉ lᵉ))
      ( λ tᵉ → fᵉ lᵉ ＝ᵉ permute-listᵉ lᵉ tᵉ)

  permutation-is-permutation-listᵉ :
    (fᵉ : listᵉ Aᵉ → listᵉ Aᵉ) → is-permutation-listᵉ fᵉ →
    ((lᵉ : listᵉ Aᵉ) → Permutationᵉ (length-listᵉ lᵉ))
  permutation-is-permutation-listᵉ fᵉ Pᵉ lᵉ = pr1ᵉ (Pᵉ lᵉ)

  eq-permute-list-permutation-is-permutation-listᵉ :
    (fᵉ : listᵉ Aᵉ → listᵉ Aᵉ) → (Pᵉ : is-permutation-listᵉ fᵉ) →
    (lᵉ : listᵉ Aᵉ) →
    (fᵉ lᵉ ＝ᵉ permute-listᵉ lᵉ (permutation-is-permutation-listᵉ fᵉ Pᵉ lᵉ))
  eq-permute-list-permutation-is-permutation-listᵉ fᵉ Pᵉ lᵉ = pr2ᵉ (Pᵉ lᵉ)
```

## Properties

### The length of a permuted list

```agda
  length-permute-listᵉ :
    (lᵉ : listᵉ Aᵉ) (tᵉ : Permutationᵉ (length-listᵉ lᵉ)) →
    length-listᵉ (permute-listᵉ lᵉ tᵉ) ＝ᵉ (length-listᵉ lᵉ)
  length-permute-listᵉ lᵉ tᵉ =
    compute-length-list-list-vecᵉ
      ( length-listᵉ lᵉ)
      ( permute-vecᵉ (length-listᵉ lᵉ) (vec-listᵉ lᵉ) tᵉ)
```

### Link between `permute-list` and `permute-vec`

```agda
  eq-vec-list-permute-listᵉ :
    (lᵉ : listᵉ Aᵉ) (fᵉ : Permutationᵉ (length-listᵉ lᵉ)) →
    permute-vecᵉ (length-listᵉ lᵉ) (vec-listᵉ lᵉ) fᵉ ＝ᵉ
    trᵉ
      ( vecᵉ Aᵉ)
      ( _)
      ( vec-listᵉ ( permute-listᵉ lᵉ fᵉ))
  eq-vec-list-permute-listᵉ lᵉ fᵉ =
    invᵉ
      ( pr2ᵉ
        ( pair-eq-Σᵉ
          ( is-retraction-vec-listᵉ
            ( (length-listᵉ lᵉ ,ᵉ permute-vecᵉ (length-listᵉ lᵉ) (vec-listᵉ lᵉ) fᵉ)))))
```

### If a function `f` from `vec` to `vec` is a permutation of vectors then `list-vec ∘ f ∘ vec-list` is a permutation of lists

```agda
  is-permutation-list-is-permutation-vecᵉ :
    (fᵉ : (nᵉ : ℕᵉ) → vecᵉ Aᵉ nᵉ → vecᵉ Aᵉ nᵉ) →
    ((nᵉ : ℕᵉ) → is-permutation-vecᵉ nᵉ (fᵉ nᵉ)) →
    is-permutation-listᵉ
      ( λ lᵉ → list-vecᵉ (length-listᵉ lᵉ) (fᵉ (length-listᵉ lᵉ) (vec-listᵉ lᵉ)))
  pr1ᵉ (is-permutation-list-is-permutation-vecᵉ fᵉ Tᵉ lᵉ) =
    pr1ᵉ (Tᵉ (length-listᵉ lᵉ) (vec-listᵉ lᵉ))
  pr2ᵉ (is-permutation-list-is-permutation-vecᵉ fᵉ Tᵉ lᵉ) =
    apᵉ (λ pᵉ → list-vecᵉ (length-listᵉ lᵉ) pᵉ) (pr2ᵉ (Tᵉ (length-listᵉ lᵉ) (vec-listᵉ lᵉ)))
```

### If `x` is in `permute-list l t` then `x` is in `l`

```agda
  is-in-list-is-in-permute-listᵉ :
    (lᵉ : listᵉ Aᵉ) (tᵉ : Permutationᵉ (length-listᵉ lᵉ)) (xᵉ : Aᵉ) →
    xᵉ ∈-listᵉ (permute-listᵉ lᵉ tᵉ) → xᵉ ∈-listᵉ lᵉ
  is-in-list-is-in-permute-listᵉ lᵉ tᵉ xᵉ Iᵉ =
    is-in-list-is-in-vec-listᵉ
      ( lᵉ)
      ( xᵉ)
      ( is-in-vec-is-in-permute-vecᵉ
        ( length-listᵉ lᵉ)
        ( vec-listᵉ lᵉ)
        ( tᵉ)
        ( xᵉ)
        ( trᵉ
          ( λ pᵉ → xᵉ ∈-vecᵉ (pr2ᵉ pᵉ))
          ( is-retraction-vec-listᵉ
            ( length-listᵉ lᵉ ,ᵉ
              permute-vecᵉ (length-listᵉ lᵉ) (vec-listᵉ lᵉ) tᵉ))
          ( is-in-vec-list-is-in-listᵉ
            ( list-vecᵉ
              ( length-listᵉ lᵉ)
              ( permute-vecᵉ (length-listᵉ lᵉ) (vec-listᵉ lᵉ) tᵉ))
            ( xᵉ)
            ( Iᵉ))))

  is-in-permute-list-is-in-listᵉ :
    (lᵉ : listᵉ Aᵉ) (tᵉ : Permutationᵉ (length-listᵉ lᵉ)) (xᵉ : Aᵉ) →
    xᵉ ∈-listᵉ lᵉ → xᵉ ∈-listᵉ (permute-listᵉ lᵉ tᵉ)
  is-in-permute-list-is-in-listᵉ lᵉ tᵉ xᵉ Iᵉ =
    is-in-list-is-in-vec-listᵉ
      ( permute-listᵉ lᵉ tᵉ)
      ( xᵉ)
      ( trᵉ
        ( λ pᵉ → xᵉ ∈-vecᵉ (pr2ᵉ pᵉ))
        ( invᵉ
          ( is-retraction-vec-listᵉ
            ( length-listᵉ lᵉ ,ᵉ permute-vecᵉ (length-listᵉ lᵉ) (vec-listᵉ lᵉ) tᵉ)))
        ( is-in-permute-vec-is-in-vecᵉ
          ( length-listᵉ lᵉ)
          ( vec-listᵉ lᵉ)
          ( tᵉ)
          ( xᵉ)
          ( is-in-vec-list-is-in-listᵉ lᵉ xᵉ Iᵉ)))
```

### If `μ : A → (B → B)` satisfies a commutativity property, then `fold-list b μ` is invariant under permutation for every `b : B`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (bᵉ : Bᵉ)
  (μᵉ : Aᵉ → (Bᵉ → Bᵉ))
  (Cᵉ : commutative-fold-vecᵉ μᵉ)
  where

  invariant-fold-vec-trᵉ :
    {nᵉ mᵉ : ℕᵉ} (vᵉ : vecᵉ Aᵉ nᵉ) (eqᵉ : nᵉ ＝ᵉ mᵉ) →
    fold-vecᵉ bᵉ μᵉ (trᵉ (vecᵉ Aᵉ) eqᵉ vᵉ) ＝ᵉ fold-vecᵉ bᵉ μᵉ vᵉ
  invariant-fold-vec-trᵉ vᵉ reflᵉ = reflᵉ

  invariant-permutation-fold-listᵉ :
    (lᵉ : listᵉ Aᵉ) → (fᵉ : Permutationᵉ (length-listᵉ lᵉ)) →
    fold-listᵉ bᵉ μᵉ lᵉ ＝ᵉ fold-listᵉ bᵉ μᵉ (permute-listᵉ lᵉ fᵉ)
  invariant-permutation-fold-listᵉ lᵉ fᵉ =
    ( invᵉ (htpy-fold-list-fold-vecᵉ bᵉ μᵉ lᵉ) ∙ᵉ
      ( invariant-permutation-fold-vecᵉ bᵉ μᵉ Cᵉ (vec-listᵉ lᵉ) fᵉ ∙ᵉ
        ( apᵉ (fold-vecᵉ bᵉ μᵉ) (eq-vec-list-permute-listᵉ lᵉ fᵉ) ∙ᵉ
          ( ( invariant-fold-vec-trᵉ
              { mᵉ = length-listᵉ lᵉ}
              ( vec-listᵉ (permute-listᵉ lᵉ fᵉ))
              ( _)) ∙ᵉ
            ( htpy-fold-list-fold-vecᵉ bᵉ μᵉ (permute-listᵉ lᵉ fᵉ))))))
```

### `map-list` of the permutation of a list

```agda
compute-tr-permute-vecᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {nᵉ mᵉ : ℕᵉ}
  (eᵉ : nᵉ ＝ᵉ mᵉ) (vᵉ : vecᵉ Aᵉ nᵉ) (tᵉ : Permutationᵉ mᵉ) →
  trᵉ
    ( vecᵉ Aᵉ)
    ( eᵉ)
    ( permute-vecᵉ
      ( nᵉ)
      ( vᵉ)
      ( trᵉ Permutationᵉ (invᵉ eᵉ) tᵉ)) ＝ᵉ
  permute-vecᵉ
    ( mᵉ)
    ( trᵉ (vecᵉ Aᵉ) eᵉ vᵉ)
    ( tᵉ)
compute-tr-permute-vecᵉ reflᵉ vᵉ tᵉ = reflᵉ

compute-tr-map-vecᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → Bᵉ) {nᵉ mᵉ : ℕᵉ} (pᵉ : nᵉ ＝ᵉ mᵉ) (vᵉ : vecᵉ Aᵉ nᵉ) →
  trᵉ (vecᵉ Bᵉ) pᵉ (map-vecᵉ fᵉ vᵉ) ＝ᵉ map-vecᵉ fᵉ (trᵉ (vecᵉ Aᵉ) pᵉ vᵉ)
compute-tr-map-vecᵉ fᵉ reflᵉ vᵉ = reflᵉ

helper-compute-list-vec-map-vec-permute-vec-vec-listᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (pᵉ : listᵉ Aᵉ) (tᵉ : Permutationᵉ (length-listᵉ pᵉ)) →
  trᵉ
    ( vecᵉ Bᵉ)
    ( invᵉ (length-permute-listᵉ pᵉ tᵉ))
    ( map-vecᵉ fᵉ (permute-vecᵉ (length-listᵉ pᵉ) (vec-listᵉ pᵉ) tᵉ)) ＝ᵉ
  map-vecᵉ fᵉ (vec-listᵉ (permute-listᵉ pᵉ tᵉ))
helper-compute-list-vec-map-vec-permute-vec-vec-listᵉ fᵉ pᵉ tᵉ =
  ( ( compute-tr-map-vecᵉ
      ( fᵉ)
      ( invᵉ (length-permute-listᵉ pᵉ tᵉ))
      ( permute-vecᵉ (length-listᵉ pᵉ) (vec-listᵉ pᵉ) tᵉ)) ∙ᵉ
    ( ( apᵉ
        ( λ Pᵉ →
          map-vecᵉ
            ( fᵉ)
            ( trᵉ (vecᵉ _) Pᵉ (permute-vecᵉ (length-listᵉ pᵉ) (vec-listᵉ pᵉ) tᵉ)))
        ( eq-is-propᵉ (is-set-ℕᵉ _ _))) ∙ᵉ
      ( apᵉ
        ( map-vecᵉ fᵉ)
        ( pr2ᵉ
          ( pair-eq-Σᵉ
            ( invᵉ
              ( is-retraction-vec-listᵉ
                ( length-listᵉ pᵉ ,ᵉ
                  permute-vecᵉ (length-listᵉ pᵉ) (vec-listᵉ pᵉ) tᵉ))))))))

compute-list-vec-map-vec-permute-vec-vec-listᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (pᵉ : listᵉ Aᵉ) (tᵉ : Permutationᵉ (length-listᵉ pᵉ)) →
  list-vecᵉ
    ( length-listᵉ pᵉ)
    ( map-vecᵉ fᵉ (permute-vecᵉ (length-listᵉ pᵉ) (vec-listᵉ pᵉ) tᵉ)) ＝ᵉ
  list-vecᵉ
    ( length-listᵉ (permute-listᵉ pᵉ tᵉ))
    ( map-vecᵉ fᵉ (vec-listᵉ (permute-listᵉ pᵉ tᵉ)))
compute-list-vec-map-vec-permute-vec-vec-listᵉ fᵉ pᵉ tᵉ =
  apᵉ
    ( λ pᵉ → list-vecᵉ (pr1ᵉ pᵉ) (pr2ᵉ pᵉ))
    ( eq-pair-Σᵉ
      ( invᵉ (length-permute-listᵉ pᵉ tᵉ))
      ( ( helper-compute-list-vec-map-vec-permute-vec-vec-listᵉ fᵉ pᵉ tᵉ)))

eq-map-list-permute-listᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (pᵉ : listᵉ Aᵉ) (tᵉ : Permutationᵉ (length-listᵉ pᵉ)) →
  permute-listᵉ (map-listᵉ fᵉ pᵉ) (trᵉ Permutationᵉ (invᵉ (length-map-listᵉ fᵉ pᵉ)) tᵉ) ＝ᵉ
  map-listᵉ fᵉ (permute-listᵉ pᵉ tᵉ)
eq-map-list-permute-listᵉ {Bᵉ = Bᵉ} fᵉ pᵉ tᵉ =
  ( ( apᵉ
      ( λ (nᵉ ,ᵉ pᵉ) → list-vecᵉ nᵉ pᵉ)
      ( eq-pair-Σᵉ
        ( length-map-listᵉ fᵉ pᵉ)
        ( ( apᵉ
            ( λ xᵉ →
              trᵉ
                ( vecᵉ Bᵉ)
                ( length-map-listᵉ fᵉ pᵉ)
                ( permute-vecᵉ
                  ( length-listᵉ (map-listᵉ fᵉ pᵉ))
                  ( xᵉ)
                  ( trᵉ Permutationᵉ (invᵉ (length-map-listᵉ fᵉ pᵉ)) tᵉ)))
            ( vec-list-map-list-map-vec-list'ᵉ fᵉ pᵉ)) ∙ᵉ
          ( ( compute-tr-permute-vecᵉ
              ( length-map-listᵉ fᵉ pᵉ)
              ( trᵉ (vecᵉ Bᵉ) (invᵉ (length-map-listᵉ fᵉ pᵉ)) (map-vecᵉ fᵉ (vec-listᵉ pᵉ)))
              ( tᵉ)) ∙ᵉ
            ( apᵉ
              ( λ vᵉ → permute-vecᵉ (length-listᵉ pᵉ) vᵉ tᵉ)
              ( is-section-inv-trᵉ
                ( vecᵉ Bᵉ)
                ( length-map-listᵉ fᵉ pᵉ)
                ( map-vecᵉ fᵉ (vec-listᵉ pᵉ)))))))) ∙ᵉ
    ( ( apᵉ
        ( list-vecᵉ (length-listᵉ pᵉ))
        ( eq-map-vec-permute-vecᵉ fᵉ (vec-listᵉ pᵉ) tᵉ)) ∙ᵉ
      ( compute-list-vec-map-vec-permute-vec-vec-listᵉ fᵉ pᵉ tᵉ ∙ᵉ
        ( map-list-map-vec-listᵉ fᵉ (permute-listᵉ pᵉ tᵉ)))))
```