# Symmetric operations

```agda
module foundation.symmetric-operationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universal-property-propositional-truncation-into-setsᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import foundation-core.coproduct-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ

open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Recallᵉ thatᵉ thereᵉ isᵉ aᵉ standardᵉ unorderedᵉ pairingᵉ operationᵉ
`{-,-ᵉ} : Aᵉ → (Aᵉ → unordered-pairᵉ A)`.ᵉ Thisᵉ inducesᵉ forᵉ anyᵉ typeᵉ `B`ᵉ aᵉ mapᵉ

```text
  λ fᵉ xᵉ yᵉ → fᵉ {x,yᵉ} : (unordered-pairᵉ Aᵉ → Bᵉ) → (Aᵉ → Aᵉ → Bᵉ)
```

Aᵉ binaryᵉ operationᵉ `μᵉ : Aᵉ → Aᵉ → B`ᵉ isᵉ symmetricᵉ ifᵉ itᵉ extendsᵉ to anᵉ operationᵉ
`μ̃ᵉ : unordered-pairᵉ Aᵉ → B`ᵉ alongᵉ `{-,-}`.ᵉ Thatᵉ is,ᵉ aᵉ binaryᵉ operationᵉ `μ`ᵉ isᵉ
symmetricᵉ ifᵉ thereᵉ isᵉ anᵉ operationᵉ `μ̃`ᵉ onᵉ theᵉ undorderedᵉ pairsᵉ in `A`,ᵉ suchᵉ thatᵉ
`μ̃({x,yᵉ}) = μ(x,y)`ᵉ forᵉ allᵉ `x,ᵉ yᵉ : A`.ᵉ Symmetricᵉ operationsᵉ canᵉ beᵉ understoodᵉ
to beᵉ fullyᵉ coherentᵉ commutativeᵉ operations.ᵉ Oneᵉ canᵉ checkᵉ thatᵉ ifᵉ `B`ᵉ isᵉ aᵉ set,ᵉ
thenᵉ `μ`ᵉ hasᵉ suchᵉ anᵉ extensionᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ commutativeᵉ in theᵉ usualᵉ
algebraicᵉ sense.ᵉ

## Definition

### The (incoherent) algebraic condition of commutativity

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-commutativeᵉ : (Aᵉ → Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-commutativeᵉ fᵉ = (xᵉ yᵉ : Aᵉ) → fᵉ xᵉ yᵉ ＝ᵉ fᵉ yᵉ xᵉ

is-commutative-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) →
  (Aᵉ → Aᵉ → type-Setᵉ Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-commutative-Propᵉ Bᵉ fᵉ =
  Π-Propᵉ _ (λ xᵉ → Π-Propᵉ _ (λ yᵉ → Id-Propᵉ Bᵉ (fᵉ xᵉ yᵉ) (fᵉ yᵉ xᵉ)))
```

### Commutative operations

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  symmetric-operationᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  symmetric-operationᵉ = unordered-pairᵉ Aᵉ → Bᵉ

  map-symmetric-operationᵉ : symmetric-operationᵉ → Aᵉ → Aᵉ → Bᵉ
  map-symmetric-operationᵉ fᵉ xᵉ yᵉ =
    fᵉ (standard-unordered-pairᵉ xᵉ yᵉ)
```

## Properties

### The restriction of a commutative operation to the standard unordered pairs is commutative

```agda
is-commutative-symmetric-operationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : symmetric-operationᵉ Aᵉ Bᵉ) →
  is-commutativeᵉ (λ xᵉ yᵉ → fᵉ (standard-unordered-pairᵉ xᵉ yᵉ))
is-commutative-symmetric-operationᵉ fᵉ xᵉ yᵉ =
  apᵉ fᵉ (is-commutative-standard-unordered-pairᵉ xᵉ yᵉ)
```

### A binary operation from `A` to `B` is commutative if and only if it extends to the unordered pairs in `A`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ)
  where

  is-weakly-constant-on-equivalences-is-commutativeᵉ :
    (fᵉ : Aᵉ → Aᵉ → type-Setᵉ Bᵉ) (Hᵉ : is-commutativeᵉ fᵉ) →
    (Xᵉ : UUᵉ lzero) (pᵉ : Xᵉ → Aᵉ) (eᵉ e'ᵉ : Finᵉ 2 ≃ᵉ Xᵉ) →
    (htpy-equivᵉ eᵉ e'ᵉ) +ᵉ (htpy-equivᵉ eᵉ (e'ᵉ ∘eᵉ equiv-succ-Finᵉ 2ᵉ)) →
    ( fᵉ (pᵉ (map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ))) (pᵉ (map-equivᵉ eᵉ (one-Finᵉ 1ᵉ)))) ＝ᵉ
    ( fᵉ (pᵉ (map-equivᵉ e'ᵉ (zero-Finᵉ 1ᵉ))) (pᵉ (map-equivᵉ e'ᵉ (one-Finᵉ 1ᵉ))))
  is-weakly-constant-on-equivalences-is-commutativeᵉ fᵉ Hᵉ Xᵉ pᵉ eᵉ e'ᵉ (inlᵉ Kᵉ) =
    ap-binaryᵉ fᵉ (apᵉ pᵉ (Kᵉ (zero-Finᵉ 1ᵉ))) (apᵉ pᵉ (Kᵉ (one-Finᵉ 1ᵉ)))
  is-weakly-constant-on-equivalences-is-commutativeᵉ fᵉ Hᵉ Xᵉ pᵉ eᵉ e'ᵉ (inrᵉ Kᵉ) =
    ( ap-binaryᵉ fᵉ (apᵉ pᵉ (Kᵉ (zero-Finᵉ 1ᵉ))) (apᵉ pᵉ (Kᵉ (one-Finᵉ 1ᵉ)))) ∙ᵉ
    ( Hᵉ (pᵉ (map-equivᵉ e'ᵉ (one-Finᵉ 1ᵉ))) (pᵉ (map-equivᵉ e'ᵉ (zero-Finᵉ 1ᵉ))))

  symmetric-operation-is-commutativeᵉ :
    (fᵉ : Aᵉ → Aᵉ → type-Setᵉ Bᵉ) → is-commutativeᵉ fᵉ →
    symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ)
  symmetric-operation-is-commutativeᵉ fᵉ Hᵉ (pairᵉ (pairᵉ Xᵉ Kᵉ) pᵉ) =
    map-universal-property-set-quotient-trunc-Propᵉ Bᵉ
      ( λ eᵉ → fᵉ (pᵉ (map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ))) (pᵉ (map-equivᵉ eᵉ (one-Finᵉ 1ᵉ))))
      ( λ eᵉ e'ᵉ →
        is-weakly-constant-on-equivalences-is-commutativeᵉ fᵉ Hᵉ Xᵉ pᵉ eᵉ e'ᵉ
          ( map-equiv-coproductᵉ
            ( inv-equivᵉ (equiv-ev-zero-htpy-equiv-Fin-two-ℕᵉ (pairᵉ Xᵉ Kᵉ) eᵉ e'ᵉ))
            ( inv-equivᵉ (equiv-ev-zero-htpy-equiv-Fin-two-ℕᵉ
              ( pairᵉ Xᵉ Kᵉ)
              ( eᵉ)
              ( e'ᵉ ∘eᵉ equiv-succ-Finᵉ 2ᵉ)))
            ( decide-value-equiv-Fin-two-ℕᵉ
              ( pairᵉ Xᵉ Kᵉ)
              ( e'ᵉ)
              ( map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ)))))
      ( Kᵉ)

  compute-symmetric-operation-is-commutativeᵉ :
    (fᵉ : Aᵉ → Aᵉ → type-Setᵉ Bᵉ) (Hᵉ : is-commutativeᵉ fᵉ) (xᵉ yᵉ : Aᵉ) →
    symmetric-operation-is-commutativeᵉ fᵉ Hᵉ (standard-unordered-pairᵉ xᵉ yᵉ) ＝ᵉ
    fᵉ xᵉ yᵉ
  compute-symmetric-operation-is-commutativeᵉ fᵉ Hᵉ xᵉ yᵉ =
    htpy-universal-property-set-quotient-trunc-Propᵉ Bᵉ
      ( λ eᵉ → fᵉ (pᵉ (map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ))) (pᵉ (map-equivᵉ eᵉ (one-Finᵉ 1ᵉ))))
      ( λ eᵉ e'ᵉ →
        is-weakly-constant-on-equivalences-is-commutativeᵉ fᵉ Hᵉ (Finᵉ 2ᵉ) pᵉ eᵉ e'ᵉ
          ( map-equiv-coproductᵉ
            ( inv-equivᵉ
              ( equiv-ev-zero-htpy-equiv-Fin-two-ℕᵉ (Fin-UU-Fin'ᵉ 2ᵉ) eᵉ e'ᵉ))
            ( inv-equivᵉ (equiv-ev-zero-htpy-equiv-Fin-two-ℕᵉ
              ( Fin-UU-Fin'ᵉ 2ᵉ)
              ( eᵉ)
              ( e'ᵉ ∘eᵉ equiv-succ-Finᵉ 2ᵉ)))
            ( decide-value-equiv-Fin-two-ℕᵉ
              ( Fin-UU-Fin'ᵉ 2ᵉ)
              ( e'ᵉ)
              ( map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ)))))
      ( id-equivᵉ)
    where
    pᵉ : Finᵉ 2 → Aᵉ
    pᵉ = pr2ᵉ (standard-unordered-pairᵉ xᵉ yᵉ)
```

### Characterization of equality of symmetric operations into sets

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Setᵉ l2ᵉ)
  (fᵉ : symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ))
  where

  htpy-symmetric-operation-Set-Propᵉ :
    (gᵉ : symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ)) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-symmetric-operation-Set-Propᵉ gᵉ =
    Π-Propᵉ Aᵉ
      ( λ xᵉ →
        Π-Propᵉ Aᵉ
          ( λ yᵉ →
            Id-Propᵉ Bᵉ
              ( map-symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ) fᵉ xᵉ yᵉ)
              ( map-symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ) gᵉ xᵉ yᵉ)))

  htpy-symmetric-operation-Setᵉ :
    (gᵉ : symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ)) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-symmetric-operation-Setᵉ gᵉ =
    type-Propᵉ (htpy-symmetric-operation-Set-Propᵉ gᵉ)

  center-total-htpy-symmetric-operation-Setᵉ :
    Σᵉ ( symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ))
      ( htpy-symmetric-operation-Setᵉ)
  pr1ᵉ center-total-htpy-symmetric-operation-Setᵉ = fᵉ
  pr2ᵉ center-total-htpy-symmetric-operation-Setᵉ xᵉ yᵉ = reflᵉ

  abstract
    contraction-total-htpy-symmetric-operation-Setᵉ :
      ( tᵉ :
        Σᵉ ( symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ))
          ( htpy-symmetric-operation-Setᵉ)) →
      center-total-htpy-symmetric-operation-Setᵉ ＝ᵉ tᵉ
    contraction-total-htpy-symmetric-operation-Setᵉ (gᵉ ,ᵉ Hᵉ) =
      eq-type-subtypeᵉ
        htpy-symmetric-operation-Set-Propᵉ
        ( eq-htpyᵉ
          ( λ pᵉ →
            apply-universal-property-trunc-Propᵉ
              ( is-surjective-standard-unordered-pairᵉ pᵉ)
              ( Id-Propᵉ Bᵉ (fᵉ pᵉ) (gᵉ pᵉ))
              ( λ where (xᵉ ,ᵉ yᵉ ,ᵉ reflᵉ) → Hᵉ xᵉ yᵉ)))

  is-torsorial-htpy-symmetric-operation-Setᵉ :
    is-torsorialᵉ (htpy-symmetric-operation-Setᵉ)
  pr1ᵉ is-torsorial-htpy-symmetric-operation-Setᵉ =
    center-total-htpy-symmetric-operation-Setᵉ
  pr2ᵉ is-torsorial-htpy-symmetric-operation-Setᵉ =
    contraction-total-htpy-symmetric-operation-Setᵉ

  htpy-eq-symmetric-operation-Setᵉ :
    (gᵉ : symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ)) →
    (fᵉ ＝ᵉ gᵉ) → htpy-symmetric-operation-Setᵉ gᵉ
  htpy-eq-symmetric-operation-Setᵉ gᵉ reflᵉ xᵉ yᵉ = reflᵉ

  is-equiv-htpy-eq-symmetric-operation-Setᵉ :
    (gᵉ : symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ)) →
    is-equivᵉ (htpy-eq-symmetric-operation-Setᵉ gᵉ)
  is-equiv-htpy-eq-symmetric-operation-Setᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-htpy-symmetric-operation-Setᵉ
      htpy-eq-symmetric-operation-Setᵉ

  extensionality-symmetric-operation-Setᵉ :
    (gᵉ : symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ)) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-symmetric-operation-Setᵉ gᵉ
  pr1ᵉ (extensionality-symmetric-operation-Setᵉ gᵉ) =
    htpy-eq-symmetric-operation-Setᵉ gᵉ
  pr2ᵉ (extensionality-symmetric-operation-Setᵉ gᵉ) =
    is-equiv-htpy-eq-symmetric-operation-Setᵉ gᵉ

  eq-htpy-symmetric-operation-Setᵉ :
    (gᵉ : symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ)) →
    htpy-symmetric-operation-Setᵉ gᵉ → (fᵉ ＝ᵉ gᵉ)
  eq-htpy-symmetric-operation-Setᵉ gᵉ =
    map-inv-equivᵉ (extensionality-symmetric-operation-Setᵉ gᵉ)
```

### The type of commutative operations into a set is equivalent to the type of symmetric operations

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Setᵉ l2ᵉ)
  where

  map-compute-symmetric-operation-Setᵉ :
    symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ) → Σᵉ (Aᵉ → Aᵉ → type-Setᵉ Bᵉ) is-commutativeᵉ
  pr1ᵉ (map-compute-symmetric-operation-Setᵉ fᵉ) =
    map-symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ) fᵉ
  pr2ᵉ (map-compute-symmetric-operation-Setᵉ fᵉ) =
    is-commutative-symmetric-operationᵉ fᵉ

  map-inv-compute-symmetric-operation-Setᵉ :
    Σᵉ (Aᵉ → Aᵉ → type-Setᵉ Bᵉ) is-commutativeᵉ → symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ)
  map-inv-compute-symmetric-operation-Setᵉ (fᵉ ,ᵉ Hᵉ) =
    symmetric-operation-is-commutativeᵉ Bᵉ fᵉ Hᵉ

  is-section-map-inv-compute-symmetric-operation-Setᵉ :
    ( map-compute-symmetric-operation-Setᵉ ∘ᵉ
      map-inv-compute-symmetric-operation-Setᵉ) ~ᵉ idᵉ
  is-section-map-inv-compute-symmetric-operation-Setᵉ (fᵉ ,ᵉ Hᵉ) =
    eq-type-subtypeᵉ
      ( is-commutative-Propᵉ Bᵉ)
      ( eq-htpyᵉ
        ( λ xᵉ →
          eq-htpyᵉ
            ( λ yᵉ →
              compute-symmetric-operation-is-commutativeᵉ Bᵉ fᵉ Hᵉ xᵉ yᵉ)))

  is-retraction-map-inv-compute-symmetric-operation-Setᵉ :
    ( map-inv-compute-symmetric-operation-Setᵉ ∘ᵉ
      map-compute-symmetric-operation-Setᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-compute-symmetric-operation-Setᵉ gᵉ =
    eq-htpy-symmetric-operation-Setᵉ Aᵉ Bᵉ
      ( map-inv-compute-symmetric-operation-Setᵉ
        ( map-compute-symmetric-operation-Setᵉ gᵉ))
      ( gᵉ)
      ( compute-symmetric-operation-is-commutativeᵉ Bᵉ
        ( map-symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ) gᵉ)
        ( is-commutative-symmetric-operationᵉ gᵉ))

  is-equiv-map-compute-symmetric-operation-Setᵉ :
    is-equivᵉ map-compute-symmetric-operation-Setᵉ
  is-equiv-map-compute-symmetric-operation-Setᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-compute-symmetric-operation-Setᵉ
      is-section-map-inv-compute-symmetric-operation-Setᵉ
      is-retraction-map-inv-compute-symmetric-operation-Setᵉ

  compute-symmetric-operation-Setᵉ :
    symmetric-operationᵉ Aᵉ (type-Setᵉ Bᵉ) ≃ᵉ Σᵉ (Aᵉ → Aᵉ → type-Setᵉ Bᵉ) is-commutativeᵉ
  pr1ᵉ compute-symmetric-operation-Setᵉ =
    map-compute-symmetric-operation-Setᵉ
  pr2ᵉ compute-symmetric-operation-Setᵉ =
    is-equiv-map-compute-symmetric-operation-Setᵉ
```