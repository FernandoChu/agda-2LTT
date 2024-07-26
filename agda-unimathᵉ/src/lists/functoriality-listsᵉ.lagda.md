# Functoriality of the list operation

```agda
module lists.functoriality-listsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.functoriality-vectorsᵉ
open import linear-algebra.vectorsᵉ

open import lists.arraysᵉ
open import lists.concatenation-listsᵉ
open import lists.listsᵉ
```

</details>

## Idea

Givenᵉ aᵉ functiionᵉ `fᵉ : Aᵉ → B`,ᵉ weᵉ obtainᵉ aᵉ functionᵉ
`map-listᵉ fᵉ : listᵉ Aᵉ → listᵉ B`.ᵉ

## Definition

```agda
map-listᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  listᵉ Aᵉ → listᵉ Bᵉ
map-listᵉ fᵉ = fold-listᵉ nilᵉ (λ aᵉ → consᵉ (fᵉ aᵉ))
```

## Properties

### `map-list` preserves the length of a list

```agda
length-map-listᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (lᵉ : listᵉ Aᵉ) →
  Idᵉ (length-listᵉ (map-listᵉ fᵉ lᵉ)) (length-listᵉ lᵉ)
length-map-listᵉ fᵉ nilᵉ = reflᵉ
length-map-listᵉ fᵉ (consᵉ xᵉ lᵉ) =
  apᵉ succ-ℕᵉ (length-map-listᵉ fᵉ lᵉ)
```

### Link between `map-list` and `map-vec`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → Bᵉ)
  where

  map-list-map-vec-listᵉ :
    (lᵉ : listᵉ Aᵉ) →
    list-vecᵉ (length-listᵉ lᵉ) (map-vecᵉ fᵉ (vec-listᵉ lᵉ)) ＝ᵉ
    map-listᵉ fᵉ lᵉ
  map-list-map-vec-listᵉ nilᵉ = reflᵉ
  map-list-map-vec-listᵉ (consᵉ xᵉ lᵉ) =
    eq-Eq-listᵉ
      ( list-vecᵉ (length-listᵉ (consᵉ xᵉ lᵉ)) (map-vecᵉ fᵉ (vec-listᵉ (consᵉ xᵉ lᵉ))))
      ( map-listᵉ fᵉ (consᵉ xᵉ lᵉ))
      ( reflᵉ ,ᵉ
        Eq-eq-listᵉ
          ( list-vecᵉ (length-listᵉ lᵉ) (map-vecᵉ fᵉ (vec-listᵉ lᵉ)))
          ( map-listᵉ fᵉ lᵉ)
          ( map-list-map-vec-listᵉ lᵉ))

  map-vec-map-list-vecᵉ :
    (nᵉ : ℕᵉ) (vᵉ : vecᵉ Aᵉ nᵉ) →
    trᵉ
      ( vecᵉ Bᵉ)
      ( length-map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ) ∙ᵉ
        compute-length-list-list-vecᵉ nᵉ vᵉ)
      ( vec-listᵉ (map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ))) ＝ᵉ
    map-vecᵉ fᵉ vᵉ
  map-vec-map-list-vecᵉ 0 empty-vecᵉ = reflᵉ
  map-vec-map-list-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ vᵉ) =
    compute-tr-vecᵉ
      ( apᵉ succ-ℕᵉ (length-map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ)) ∙ᵉ
        compute-length-list-list-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ vᵉ))
      ( vec-listᵉ (fold-listᵉ nilᵉ (λ aᵉ → consᵉ (fᵉ aᵉ)) (list-vecᵉ nᵉ vᵉ)))
      ( fᵉ xᵉ) ∙ᵉ
    eq-Eq-vecᵉ
      ( succ-ℕᵉ nᵉ)
      ( fᵉ xᵉ ∷ᵉ
        trᵉ
          ( vecᵉ Bᵉ)
          ( is-injective-succ-ℕᵉ
            ( apᵉ succ-ℕᵉ (length-map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ)) ∙ᵉ
              compute-length-list-list-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ vᵉ)))
          ( vec-listᵉ (map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ))))
      ( map-vecᵉ fᵉ (xᵉ ∷ᵉ vᵉ))
      ( reflᵉ ,ᵉ
        ( Eq-eq-vecᵉ
          ( nᵉ)
          ( trᵉ
            ( vecᵉ Bᵉ)
            ( is-injective-succ-ℕᵉ
              ( apᵉ succ-ℕᵉ (length-map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ)) ∙ᵉ
                compute-length-list-list-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ vᵉ)))
            ( vec-listᵉ (map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ))))
          ( map-vecᵉ fᵉ vᵉ)
          ( trᵉ
            ( λ pᵉ →
              trᵉ
                ( vecᵉ Bᵉ)
                ( pᵉ)
                ( vec-listᵉ (map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ))) ＝ᵉ
              map-vecᵉ fᵉ vᵉ)
            ( eq-is-propᵉ
              ( is-set-ℕᵉ
                ( length-listᵉ (map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ)))
                ( nᵉ)))
            ( map-vec-map-list-vecᵉ nᵉ vᵉ))))

  map-vec-map-list-vec'ᵉ :
    (nᵉ : ℕᵉ) (vᵉ : vecᵉ Aᵉ nᵉ) →
    vec-listᵉ (map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ)) ＝ᵉ
    trᵉ
      ( vecᵉ Bᵉ)
      ( invᵉ
        ( length-map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ) ∙ᵉ
          compute-length-list-list-vecᵉ nᵉ vᵉ))
      ( map-vecᵉ fᵉ vᵉ)
  map-vec-map-list-vec'ᵉ nᵉ vᵉ =
    eq-transpose-tr'ᵉ
      ( length-map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ) ∙ᵉ compute-length-list-list-vecᵉ nᵉ vᵉ)
      ( map-vec-map-list-vecᵉ nᵉ vᵉ)

  vec-list-map-list-map-vec-listᵉ :
    (lᵉ : listᵉ Aᵉ) →
    trᵉ
      ( vecᵉ Bᵉ)
      ( length-map-listᵉ fᵉ lᵉ)
      ( vec-listᵉ (map-listᵉ fᵉ lᵉ)) ＝ᵉ
    map-vecᵉ fᵉ (vec-listᵉ lᵉ)
  vec-list-map-list-map-vec-listᵉ nilᵉ = reflᵉ
  vec-list-map-list-map-vec-listᵉ (consᵉ xᵉ lᵉ) =
    compute-tr-vecᵉ
      ( apᵉ succ-ℕᵉ (length-map-listᵉ fᵉ lᵉ))
      ( vec-listᵉ (map-listᵉ fᵉ lᵉ))
      ( fᵉ xᵉ) ∙ᵉ
    eq-Eq-vecᵉ
      ( succ-ℕᵉ (length-listᵉ lᵉ))
      ( fᵉ xᵉ ∷ᵉ
        trᵉ
          ( vecᵉ Bᵉ)
          ( is-injective-succ-ℕᵉ (apᵉ succ-ℕᵉ (length-map-listᵉ fᵉ lᵉ)))
          ( vec-listᵉ (map-listᵉ fᵉ lᵉ)))
      ( map-vecᵉ fᵉ (vec-listᵉ (consᵉ xᵉ lᵉ)))
      ( reflᵉ ,ᵉ
        Eq-eq-vecᵉ
          ( length-listᵉ lᵉ)
          ( trᵉ
            ( vecᵉ Bᵉ)
            ( is-injective-succ-ℕᵉ (apᵉ succ-ℕᵉ (length-map-listᵉ fᵉ lᵉ)))
            ( vec-listᵉ (map-listᵉ fᵉ lᵉ)))
          ( map-vecᵉ fᵉ (vec-listᵉ lᵉ))
          ( trᵉ
            ( λ pᵉ →
              ( trᵉ
                ( vecᵉ Bᵉ)
                ( pᵉ)
                ( vec-listᵉ (map-listᵉ fᵉ lᵉ))) ＝ᵉ
              ( map-vecᵉ fᵉ (vec-listᵉ lᵉ)))
            ( eq-is-propᵉ
              ( is-set-ℕᵉ (length-listᵉ (map-listᵉ fᵉ lᵉ)) (length-listᵉ lᵉ)))
            ( vec-list-map-list-map-vec-listᵉ lᵉ)))

  vec-list-map-list-map-vec-list'ᵉ :
    (lᵉ : listᵉ Aᵉ) →
    vec-listᵉ (map-listᵉ fᵉ lᵉ) ＝ᵉ
    trᵉ
      ( vecᵉ Bᵉ)
      ( invᵉ (length-map-listᵉ fᵉ lᵉ))
      ( map-vecᵉ fᵉ (vec-listᵉ lᵉ))
  vec-list-map-list-map-vec-list'ᵉ lᵉ =
    eq-transpose-tr'ᵉ
      ( length-map-listᵉ fᵉ lᵉ)
      ( vec-list-map-list-map-vec-listᵉ lᵉ)

  list-vec-map-vec-map-list-vecᵉ :
    (nᵉ : ℕᵉ) (vᵉ : vecᵉ Aᵉ nᵉ) →
    list-vecᵉ
      ( length-listᵉ (map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ)))
      ( vec-listᵉ (map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ))) ＝ᵉ
    list-vecᵉ nᵉ (map-vecᵉ fᵉ vᵉ)
  list-vec-map-vec-map-list-vecᵉ nᵉ vᵉ =
    apᵉ
      ( λ pᵉ → list-vecᵉ (pr1ᵉ pᵉ) (pr2ᵉ pᵉ))
      ( eq-pair-Σᵉ
        ( length-map-listᵉ fᵉ (list-vecᵉ nᵉ vᵉ) ∙ᵉ
          compute-length-list-list-vecᵉ nᵉ vᵉ)
        ( map-vec-map-list-vecᵉ nᵉ vᵉ))
```

### `map-list` preserves concatenation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  preserves-concat-map-listᵉ :
    (lᵉ kᵉ : listᵉ Aᵉ) →
    Idᵉ
      ( map-listᵉ fᵉ (concat-listᵉ lᵉ kᵉ))
      ( concat-listᵉ (map-listᵉ fᵉ lᵉ) (map-listᵉ fᵉ kᵉ))
  preserves-concat-map-listᵉ nilᵉ kᵉ = reflᵉ
  preserves-concat-map-listᵉ (consᵉ xᵉ lᵉ) kᵉ =
    apᵉ (consᵉ (fᵉ xᵉ)) (preserves-concat-map-listᵉ lᵉ kᵉ)
```

### Functoriality of the list operation

Firstᵉ weᵉ introduceᵉ theᵉ functorialityᵉ ofᵉ theᵉ listᵉ operation,ᵉ becauseᵉ itᵉ willᵉ comeᵉ
in handyᵉ whenᵉ weᵉ tryᵉ to defineᵉ andᵉ proveᵉ moreᵉ advancedᵉ things.ᵉ

```agda
identity-law-map-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  map-listᵉ (idᵉ {Aᵉ = Aᵉ}) ~ᵉ idᵉ
identity-law-map-listᵉ nilᵉ = reflᵉ
identity-law-map-listᵉ (consᵉ aᵉ xᵉ) =
  apᵉ (consᵉ aᵉ) (identity-law-map-listᵉ xᵉ)

composition-law-map-listᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} →
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Cᵉ) →
  map-listᵉ (gᵉ ∘ᵉ fᵉ) ~ᵉ (map-listᵉ gᵉ ∘ᵉ map-listᵉ fᵉ)
composition-law-map-listᵉ fᵉ gᵉ nilᵉ = reflᵉ
composition-law-map-listᵉ fᵉ gᵉ (consᵉ aᵉ xᵉ) =
  apᵉ (consᵉ (gᵉ (fᵉ aᵉ))) (composition-law-map-listᵉ fᵉ gᵉ xᵉ)
```

### `map-list` applied to lists of the form `snoc x a`

```agda
map-snoc-listᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (xᵉ : listᵉ Aᵉ) (aᵉ : Aᵉ) →
  map-listᵉ fᵉ (snocᵉ xᵉ aᵉ) ＝ᵉ snocᵉ (map-listᵉ fᵉ xᵉ) (fᵉ aᵉ)
map-snoc-listᵉ fᵉ nilᵉ aᵉ = reflᵉ
map-snoc-listᵉ fᵉ (consᵉ bᵉ xᵉ) aᵉ = apᵉ (consᵉ (fᵉ bᵉ)) (map-snoc-listᵉ fᵉ xᵉ aᵉ)
```