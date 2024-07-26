# Finitely graded posets

```agda
module order-theory.finitely-graded-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-typesᵉ
open import elementary-number-theory.modular-arithmeticᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.binary-relationsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.bottom-elements-posetsᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
open import order-theory.top-elements-posetsᵉ
open import order-theory.total-ordersᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ **finitelyᵉ gradedᵉ poset**ᵉ consistsᵉ ofᵉ aᵉ familyᵉ ofᵉ typesᵉ indexedᵉ byᵉ
`Finᵉ (succ-ℕᵉ k)`ᵉ equippedᵉ with anᵉ orderingᵉ relationᵉ fromᵉ `Finᵉ (inlᵉ i)`ᵉ to
`Finᵉ (succ-Finᵉ (inlᵉ i))`ᵉ forᵉ eachᵉ `iᵉ : Finᵉ k`.ᵉ

```agda
Finitely-Graded-Posetᵉ : (l1ᵉ l2ᵉ : Level) (kᵉ : ℕᵉ) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ =
  Σᵉ ( Finᵉ (succ-ℕᵉ kᵉ) → Setᵉ l1ᵉ)
    ( λ Xᵉ →
      (iᵉ : Finᵉ kᵉ) → type-Setᵉ (Xᵉ (inl-Finᵉ kᵉ iᵉ)) →
      type-Setᵉ (Xᵉ (succ-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ iᵉ))) → Propᵉ l2ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ)
  where

  module _
    (iᵉ : Finᵉ (succ-ℕᵉ kᵉ))
    where

    face-Finitely-Graded-Poset-Setᵉ : Setᵉ l1ᵉ
    face-Finitely-Graded-Poset-Setᵉ = pr1ᵉ Xᵉ iᵉ

    face-Finitely-Graded-Posetᵉ : UUᵉ l1ᵉ
    face-Finitely-Graded-Posetᵉ =
      type-Setᵉ face-Finitely-Graded-Poset-Setᵉ

    is-set-face-Finitely-Graded-Posetᵉ :
      is-setᵉ face-Finitely-Graded-Posetᵉ
    is-set-face-Finitely-Graded-Posetᵉ =
      is-set-type-Setᵉ face-Finitely-Graded-Poset-Setᵉ

  module _
    (iᵉ : Finᵉ kᵉ) (yᵉ : face-Finitely-Graded-Posetᵉ (inl-Finᵉ kᵉ iᵉ))
    (zᵉ : face-Finitely-Graded-Posetᵉ (succ-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ iᵉ)))
    where

    adjacent-Finitely-Graded-Poset-Propᵉ : Propᵉ l2ᵉ
    adjacent-Finitely-Graded-Poset-Propᵉ = pr2ᵉ Xᵉ iᵉ yᵉ zᵉ

    adjacent-Finitely-Graded-Posetᵉ : UUᵉ l2ᵉ
    adjacent-Finitely-Graded-Posetᵉ =
      type-Propᵉ adjacent-Finitely-Graded-Poset-Propᵉ

    is-prop-adjacent-Finitely-Graded-Posetᵉ :
      is-propᵉ adjacent-Finitely-Graded-Posetᵉ
    is-prop-adjacent-Finitely-Graded-Posetᵉ =
      is-prop-type-Propᵉ adjacent-Finitely-Graded-Poset-Propᵉ

  set-Finitely-Graded-Posetᵉ : Setᵉ l1ᵉ
  set-Finitely-Graded-Posetᵉ =
    Σ-Setᵉ (Fin-Setᵉ (succ-ℕᵉ kᵉ)) face-Finitely-Graded-Poset-Setᵉ

  type-Finitely-Graded-Posetᵉ : UUᵉ l1ᵉ
  type-Finitely-Graded-Posetᵉ = type-Setᵉ set-Finitely-Graded-Posetᵉ

  is-set-type-Finitely-Graded-Posetᵉ : is-setᵉ type-Finitely-Graded-Posetᵉ
  is-set-type-Finitely-Graded-Posetᵉ =
    is-set-type-Setᵉ set-Finitely-Graded-Posetᵉ

  element-face-Finitely-Graded-Posetᵉ :
    {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Finitely-Graded-Posetᵉ iᵉ →
    type-Finitely-Graded-Posetᵉ
  element-face-Finitely-Graded-Posetᵉ {iᵉ} xᵉ = pairᵉ iᵉ xᵉ

  shape-Finitely-Graded-Posetᵉ :
    type-Finitely-Graded-Posetᵉ → Finᵉ (succ-ℕᵉ kᵉ)
  shape-Finitely-Graded-Posetᵉ (pairᵉ iᵉ xᵉ) = iᵉ

  face-type-Finitely-Graded-Posetᵉ :
    (xᵉ : type-Finitely-Graded-Posetᵉ) →
    face-Finitely-Graded-Posetᵉ (shape-Finitely-Graded-Posetᵉ xᵉ)
  face-type-Finitely-Graded-Posetᵉ (pairᵉ iᵉ xᵉ) = xᵉ

  module _
    {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} (xᵉ : face-Finitely-Graded-Posetᵉ iᵉ)
    where
```

Ifᵉ chainsᵉ with jumpsᵉ areᵉ neverᵉ used,ᵉ we'dᵉ likeᵉ to callᵉ theᵉ followingᵉ chains.ᵉ

```agda
    data
      path-faces-Finitely-Graded-Posetᵉ :
        {jᵉ : Finᵉ (succ-ℕᵉ kᵉ)} (yᵉ : face-Finitely-Graded-Posetᵉ jᵉ) →
        UUᵉ (l1ᵉ ⊔ l2ᵉ)
        where
        refl-path-faces-Finitely-Graded-Posetᵉ :
          path-faces-Finitely-Graded-Posetᵉ xᵉ
        cons-path-faces-Finitely-Graded-Posetᵉ :
          {jᵉ : Finᵉ kᵉ} {yᵉ : face-Finitely-Graded-Posetᵉ (inl-Finᵉ kᵉ jᵉ)}
          {zᵉ : face-Finitely-Graded-Posetᵉ (succ-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ jᵉ))} →
          adjacent-Finitely-Graded-Posetᵉ jᵉ yᵉ zᵉ →
          path-faces-Finitely-Graded-Posetᵉ yᵉ →
          path-faces-Finitely-Graded-Posetᵉ zᵉ

  tr-refl-path-faces-Finitely-Graded-Posetᵉ :
    {iᵉ jᵉ : Finᵉ (succ-ℕᵉ kᵉ)} (pᵉ : Idᵉ jᵉ iᵉ) (xᵉ : face-Finitely-Graded-Posetᵉ jᵉ) →
    path-faces-Finitely-Graded-Posetᵉ
      ( trᵉ face-Finitely-Graded-Posetᵉ pᵉ xᵉ)
      ( xᵉ)
  tr-refl-path-faces-Finitely-Graded-Posetᵉ reflᵉ xᵉ =
    refl-path-faces-Finitely-Graded-Posetᵉ

  concat-path-faces-Finitely-Graded-Posetᵉ :
    {i1ᵉ i2ᵉ i3ᵉ : Finᵉ (succ-ℕᵉ kᵉ)}
    {xᵉ : face-Finitely-Graded-Posetᵉ i1ᵉ}
    {yᵉ : face-Finitely-Graded-Posetᵉ i2ᵉ}
    {zᵉ : face-Finitely-Graded-Posetᵉ i3ᵉ} →
    path-faces-Finitely-Graded-Posetᵉ yᵉ zᵉ →
    path-faces-Finitely-Graded-Posetᵉ xᵉ yᵉ →
    path-faces-Finitely-Graded-Posetᵉ xᵉ zᵉ
  concat-path-faces-Finitely-Graded-Posetᵉ
    refl-path-faces-Finitely-Graded-Posetᵉ Kᵉ = Kᵉ
  concat-path-faces-Finitely-Graded-Posetᵉ
    ( cons-path-faces-Finitely-Graded-Posetᵉ xᵉ Hᵉ) Kᵉ =
    cons-path-faces-Finitely-Graded-Posetᵉ xᵉ
      ( concat-path-faces-Finitely-Graded-Posetᵉ Hᵉ Kᵉ)

  path-elements-Finitely-Graded-Posetᵉ :
    (xᵉ yᵉ : type-Finitely-Graded-Posetᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  path-elements-Finitely-Graded-Posetᵉ (pairᵉ iᵉ xᵉ) (pairᵉ jᵉ yᵉ) =
    path-faces-Finitely-Graded-Posetᵉ xᵉ yᵉ

  refl-path-elements-Finitely-Graded-Posetᵉ :
    (xᵉ : type-Finitely-Graded-Posetᵉ) →
    path-elements-Finitely-Graded-Posetᵉ xᵉ xᵉ
  refl-path-elements-Finitely-Graded-Posetᵉ xᵉ =
    refl-path-faces-Finitely-Graded-Posetᵉ

  concat-path-elements-Finitely-Graded-Posetᵉ :
    (xᵉ yᵉ zᵉ : type-Finitely-Graded-Posetᵉ) →
    path-elements-Finitely-Graded-Posetᵉ yᵉ zᵉ →
    path-elements-Finitely-Graded-Posetᵉ xᵉ yᵉ →
    path-elements-Finitely-Graded-Posetᵉ xᵉ zᵉ
  concat-path-elements-Finitely-Graded-Posetᵉ xᵉ yᵉ zᵉ =
    concat-path-faces-Finitely-Graded-Posetᵉ

  leq-type-path-faces-Finitely-Graded-Posetᵉ :
    {i1ᵉ i2ᵉ : Finᵉ (succ-ℕᵉ kᵉ)} (xᵉ : face-Finitely-Graded-Posetᵉ i1ᵉ)
    (yᵉ : face-Finitely-Graded-Posetᵉ i2ᵉ) →
    path-faces-Finitely-Graded-Posetᵉ xᵉ yᵉ → leq-Finᵉ (succ-ℕᵉ kᵉ) i1ᵉ i2ᵉ
  leq-type-path-faces-Finitely-Graded-Posetᵉ {i1ᵉ} xᵉ .xᵉ
    refl-path-faces-Finitely-Graded-Posetᵉ = refl-leq-Finᵉ (succ-ℕᵉ kᵉ) i1ᵉ
  leq-type-path-faces-Finitely-Graded-Posetᵉ {i1ᵉ} xᵉ yᵉ
    ( cons-path-faces-Finitely-Graded-Posetᵉ {i3ᵉ} {zᵉ} Hᵉ Kᵉ) =
    transitive-leq-Finᵉ
      ( succ-ℕᵉ kᵉ)
      ( i1ᵉ)
      ( inl-Finᵉ kᵉ i3ᵉ)
      ( succ-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ i3ᵉ))
      ( leq-succ-Finᵉ kᵉ i3ᵉ)
      ( leq-type-path-faces-Finitely-Graded-Posetᵉ xᵉ zᵉ Kᵉ)
```

### Antisymmetry of path-elements-Finitely-Graded-Poset

```agda
eq-path-elements-Finitely-Graded-Posetᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ)
  (xᵉ yᵉ : type-Finitely-Graded-Posetᵉ Xᵉ) →
  (pᵉ : Idᵉ (shape-Finitely-Graded-Posetᵉ Xᵉ xᵉ)
          (shape-Finitely-Graded-Posetᵉ Xᵉ yᵉ)) →
  path-elements-Finitely-Graded-Posetᵉ Xᵉ xᵉ yᵉ → Idᵉ xᵉ yᵉ
eq-path-elements-Finitely-Graded-Posetᵉ {kᵉ} Xᵉ (pairᵉ i1ᵉ xᵉ) (pairᵉ .i1ᵉ .xᵉ) pᵉ
  refl-path-faces-Finitely-Graded-Posetᵉ = reflᵉ
eq-path-elements-Finitely-Graded-Posetᵉ {kᵉ = succ-ℕᵉ kᵉ} Xᵉ (pairᵉ i1ᵉ xᵉ)
  (pairᵉ .(succ-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) (inl-Finᵉ (succ-ℕᵉ kᵉ) i2ᵉ)) yᵉ) pᵉ
  (cons-path-faces-Finitely-Graded-Posetᵉ {i2ᵉ} {zᵉ} Hᵉ Kᵉ) =
  ex-falsoᵉ
    ( has-no-fixed-points-succ-Finᵉ
      { succ-ℕᵉ (succ-ℕᵉ kᵉ)}
      ( inl-Finᵉ (succ-ℕᵉ kᵉ) i2ᵉ)
      ( λ (qᵉ : is-one-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ))) →
        is-nonzero-succ-ℕᵉ kᵉ (is-injective-succ-ℕᵉ qᵉ))
      ( antisymmetric-leq-Finᵉ
        ( succ-ℕᵉ (succ-ℕᵉ kᵉ))
        ( succ-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) (inl-Finᵉ (succ-ℕᵉ kᵉ) i2ᵉ))
        ( inl-Finᵉ (succ-ℕᵉ kᵉ) i2ᵉ)
        ( transitive-leq-Finᵉ
          ( succ-ℕᵉ (succ-ℕᵉ kᵉ))
          ( skip-zero-Finᵉ (succ-ℕᵉ kᵉ) i2ᵉ)
          ( i1ᵉ)
          ( inlᵉ i2ᵉ)
          ( leq-type-path-faces-Finitely-Graded-Posetᵉ Xᵉ xᵉ zᵉ Kᵉ)
          ( trᵉ
            ( leq-Finᵉ
              ( succ-ℕᵉ (succ-ℕᵉ kᵉ))
              ( succ-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) (inl-Finᵉ (succ-ℕᵉ kᵉ) i2ᵉ)))
            ( invᵉ pᵉ)
            ( refl-leq-Finᵉ
              ( succ-ℕᵉ (succ-ℕᵉ kᵉ))
              ( succ-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) (inl-Finᵉ (succ-ℕᵉ kᵉ) i2ᵉ)))))
        ( leq-succ-Finᵉ (succ-ℕᵉ kᵉ) i2ᵉ)))

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ)
  where

  abstract
    eq-path-faces-Finitely-Graded-Posetᵉ :
      {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} (xᵉ yᵉ : face-Finitely-Graded-Posetᵉ Xᵉ iᵉ) →
      path-faces-Finitely-Graded-Posetᵉ Xᵉ xᵉ yᵉ → Idᵉ xᵉ yᵉ
    eq-path-faces-Finitely-Graded-Posetᵉ {iᵉ} xᵉ yᵉ Hᵉ =
      map-left-unit-law-Σ-is-contrᵉ
        ( is-proof-irrelevant-is-propᵉ
          ( is-set-Finᵉ (succ-ℕᵉ kᵉ) iᵉ iᵉ)
          ( reflᵉ))
        ( reflᵉ)
        ( pair-eq-Σᵉ
          ( eq-path-elements-Finitely-Graded-Posetᵉ Xᵉ
            ( element-face-Finitely-Graded-Posetᵉ Xᵉ xᵉ)
            ( element-face-Finitely-Graded-Posetᵉ Xᵉ yᵉ)
            ( reflᵉ)
            ( Hᵉ)))

  antisymmetric-path-elements-Finitely-Graded-Posetᵉ :
    (xᵉ yᵉ : type-Finitely-Graded-Posetᵉ Xᵉ) →
    path-elements-Finitely-Graded-Posetᵉ Xᵉ xᵉ yᵉ →
    path-elements-Finitely-Graded-Posetᵉ Xᵉ yᵉ xᵉ →
    Idᵉ xᵉ yᵉ
  antisymmetric-path-elements-Finitely-Graded-Posetᵉ (pairᵉ iᵉ xᵉ) (pairᵉ jᵉ yᵉ) Hᵉ Kᵉ =
    eq-path-elements-Finitely-Graded-Posetᵉ Xᵉ (pairᵉ iᵉ xᵉ) (pairᵉ jᵉ yᵉ)
      ( antisymmetric-leq-Finᵉ (succ-ℕᵉ kᵉ)
        ( shape-Finitely-Graded-Posetᵉ Xᵉ (pairᵉ iᵉ xᵉ))
        ( shape-Finitely-Graded-Posetᵉ Xᵉ (pairᵉ jᵉ yᵉ))
        ( leq-type-path-faces-Finitely-Graded-Posetᵉ Xᵉ xᵉ yᵉ Hᵉ)
        ( leq-type-path-faces-Finitely-Graded-Posetᵉ Xᵉ yᵉ xᵉ Kᵉ))
      ( Hᵉ)
```

### Poset structure on the underlying type of a finitely graded poset

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ)
  where

  module _
    (xᵉ yᵉ : type-Finitely-Graded-Posetᵉ Xᵉ)
    where

    leq-Finitely-Graded-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
    leq-Finitely-Graded-Poset-Propᵉ =
      trunc-Propᵉ (path-elements-Finitely-Graded-Posetᵉ Xᵉ xᵉ yᵉ)

    leq-Finitely-Graded-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    leq-Finitely-Graded-Posetᵉ = type-Propᵉ leq-Finitely-Graded-Poset-Propᵉ

    is-prop-leq-Finitely-Graded-Posetᵉ : is-propᵉ leq-Finitely-Graded-Posetᵉ
    is-prop-leq-Finitely-Graded-Posetᵉ =
      is-prop-type-Propᵉ leq-Finitely-Graded-Poset-Propᵉ

  refl-leq-Finitely-Graded-Posetᵉ :
    is-reflexiveᵉ leq-Finitely-Graded-Posetᵉ
  refl-leq-Finitely-Graded-Posetᵉ xᵉ =
    unit-trunc-Propᵉ (refl-path-elements-Finitely-Graded-Posetᵉ Xᵉ xᵉ)

  transitive-leq-Finitely-Graded-Posetᵉ :
    is-transitiveᵉ leq-Finitely-Graded-Posetᵉ
  transitive-leq-Finitely-Graded-Posetᵉ xᵉ yᵉ zᵉ Hᵉ Kᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( leq-Finitely-Graded-Poset-Propᵉ xᵉ zᵉ)
      ( λ Lᵉ →
        apply-universal-property-trunc-Propᵉ Kᵉ
          ( leq-Finitely-Graded-Poset-Propᵉ xᵉ zᵉ)
          ( λ Mᵉ →
            unit-trunc-Propᵉ
              ( concat-path-elements-Finitely-Graded-Posetᵉ Xᵉ xᵉ yᵉ zᵉ Lᵉ Mᵉ)))

  antisymmetric-leq-Finitely-Graded-Posetᵉ :
    is-antisymmetricᵉ leq-Finitely-Graded-Posetᵉ
  antisymmetric-leq-Finitely-Graded-Posetᵉ xᵉ yᵉ Hᵉ Kᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( Id-Propᵉ (set-Finitely-Graded-Posetᵉ Xᵉ) xᵉ yᵉ)
      ( λ Lᵉ →
        apply-universal-property-trunc-Propᵉ Kᵉ
          ( Id-Propᵉ (set-Finitely-Graded-Posetᵉ Xᵉ) xᵉ yᵉ)
          ( λ Mᵉ →
            antisymmetric-path-elements-Finitely-Graded-Posetᵉ Xᵉ xᵉ yᵉ Lᵉ Mᵉ))

  preorder-Finitely-Graded-Posetᵉ : Preorderᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ preorder-Finitely-Graded-Posetᵉ = type-Finitely-Graded-Posetᵉ Xᵉ
  pr1ᵉ (pr2ᵉ preorder-Finitely-Graded-Posetᵉ) = leq-Finitely-Graded-Poset-Propᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ preorder-Finitely-Graded-Posetᵉ)) =
    refl-leq-Finitely-Graded-Posetᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ preorder-Finitely-Graded-Posetᵉ)) =
    transitive-leq-Finitely-Graded-Posetᵉ

  poset-Finitely-Graded-Posetᵉ : Posetᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ poset-Finitely-Graded-Posetᵉ = preorder-Finitely-Graded-Posetᵉ
  pr2ᵉ poset-Finitely-Graded-Posetᵉ = antisymmetric-leq-Finitely-Graded-Posetᵉ
```

### Least and largest elements in finitely graded posets

Weᵉ makeᵉ sureᵉ thatᵉ theᵉ leastᵉ elementᵉ isᵉ aᵉ faceᵉ ofᵉ typeᵉ zero-Fin,ᵉ andᵉ thatᵉ theᵉ
largestᵉ elementᵉ isᵉ aᵉ faceᵉ ofᵉ typeᵉ neg-one-Fin.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ)
  where

  module _
    (xᵉ : face-Finitely-Graded-Posetᵉ Xᵉ (zero-Finᵉ kᵉ))
    where

    is-bottom-element-Finitely-Graded-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
    is-bottom-element-Finitely-Graded-Poset-Propᵉ =
      is-bottom-element-Poset-Propᵉ
        ( poset-Finitely-Graded-Posetᵉ Xᵉ)
        ( element-face-Finitely-Graded-Posetᵉ Xᵉ xᵉ)

    is-bottom-element-Finitely-Graded-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    is-bottom-element-Finitely-Graded-Posetᵉ =
      is-bottom-element-Posetᵉ
        ( poset-Finitely-Graded-Posetᵉ Xᵉ)
        ( element-face-Finitely-Graded-Posetᵉ Xᵉ xᵉ)

    is-prop-is-bottom-element-Finitely-Graded-Posetᵉ :
      is-propᵉ is-bottom-element-Finitely-Graded-Posetᵉ
    is-prop-is-bottom-element-Finitely-Graded-Posetᵉ =
      is-prop-is-bottom-element-Posetᵉ
        ( poset-Finitely-Graded-Posetᵉ Xᵉ)
        ( element-face-Finitely-Graded-Posetᵉ Xᵉ xᵉ)

  has-bottom-element-Finitely-Graded-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-bottom-element-Finitely-Graded-Posetᵉ =
    Σᵉ ( face-Finitely-Graded-Posetᵉ Xᵉ (zero-Finᵉ kᵉ))
      ( is-bottom-element-Finitely-Graded-Posetᵉ)

  all-elements-equal-has-bottom-element-Finitely-Graded-Posetᵉ :
    all-elements-equalᵉ has-bottom-element-Finitely-Graded-Posetᵉ
  all-elements-equal-has-bottom-element-Finitely-Graded-Posetᵉ
    ( pairᵉ xᵉ Hᵉ)
    ( pairᵉ yᵉ Kᵉ) =
    eq-type-subtypeᵉ
      ( is-bottom-element-Finitely-Graded-Poset-Propᵉ)
      ( apply-universal-property-trunc-Propᵉ
        ( Hᵉ (element-face-Finitely-Graded-Posetᵉ Xᵉ yᵉ))
        ( Id-Propᵉ (face-Finitely-Graded-Poset-Setᵉ Xᵉ (zero-Finᵉ kᵉ)) xᵉ yᵉ)
        ( eq-path-faces-Finitely-Graded-Posetᵉ Xᵉ xᵉ yᵉ))

  is-prop-has-bottom-element-Finitely-Graded-Posetᵉ :
    is-propᵉ has-bottom-element-Finitely-Graded-Posetᵉ
  is-prop-has-bottom-element-Finitely-Graded-Posetᵉ =
    is-prop-all-elements-equalᵉ
      all-elements-equal-has-bottom-element-Finitely-Graded-Posetᵉ

  has-bottom-element-Finitely-Graded-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ has-bottom-element-Finitely-Graded-Poset-Propᵉ =
    has-bottom-element-Finitely-Graded-Posetᵉ
  pr2ᵉ has-bottom-element-Finitely-Graded-Poset-Propᵉ =
    is-prop-has-bottom-element-Finitely-Graded-Posetᵉ

  module _
    (xᵉ : face-Finitely-Graded-Posetᵉ Xᵉ (neg-one-Finᵉ kᵉ))
    where

    is-top-element-Finitely-Graded-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
    is-top-element-Finitely-Graded-Poset-Propᵉ =
      is-top-element-Poset-Propᵉ
        ( poset-Finitely-Graded-Posetᵉ Xᵉ)
        ( element-face-Finitely-Graded-Posetᵉ Xᵉ xᵉ)

    is-top-element-Finitely-Graded-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    is-top-element-Finitely-Graded-Posetᵉ =
      is-top-element-Posetᵉ
        ( poset-Finitely-Graded-Posetᵉ Xᵉ)
        ( element-face-Finitely-Graded-Posetᵉ Xᵉ xᵉ)

    is-prop-is-top-element-Finitely-Graded-Posetᵉ :
      is-propᵉ is-top-element-Finitely-Graded-Posetᵉ
    is-prop-is-top-element-Finitely-Graded-Posetᵉ =
      is-prop-is-top-element-Posetᵉ
        ( poset-Finitely-Graded-Posetᵉ Xᵉ)
        ( element-face-Finitely-Graded-Posetᵉ Xᵉ xᵉ)

  has-top-element-Finitely-Graded-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-top-element-Finitely-Graded-Posetᵉ =
    Σᵉ ( face-Finitely-Graded-Posetᵉ Xᵉ (neg-one-Finᵉ kᵉ))
      ( is-top-element-Finitely-Graded-Posetᵉ)

  all-elements-equal-has-top-element-Finitely-Graded-Posetᵉ :
    all-elements-equalᵉ has-top-element-Finitely-Graded-Posetᵉ
  all-elements-equal-has-top-element-Finitely-Graded-Posetᵉ
    (pairᵉ xᵉ Hᵉ) (pairᵉ yᵉ Kᵉ) =
    eq-type-subtypeᵉ
      ( is-top-element-Finitely-Graded-Poset-Propᵉ)
      ( apply-universal-property-trunc-Propᵉ
        ( Kᵉ (element-face-Finitely-Graded-Posetᵉ Xᵉ xᵉ))
        ( Id-Propᵉ (face-Finitely-Graded-Poset-Setᵉ Xᵉ (neg-one-Finᵉ kᵉ)) xᵉ yᵉ)
        ( eq-path-faces-Finitely-Graded-Posetᵉ Xᵉ xᵉ yᵉ))

  is-prop-has-top-element-Finitely-Graded-Posetᵉ :
    is-propᵉ has-top-element-Finitely-Graded-Posetᵉ
  is-prop-has-top-element-Finitely-Graded-Posetᵉ =
    is-prop-all-elements-equalᵉ
      all-elements-equal-has-top-element-Finitely-Graded-Posetᵉ

  has-top-element-Finitely-Graded-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ has-top-element-Finitely-Graded-Poset-Propᵉ =
    has-top-element-Finitely-Graded-Posetᵉ
  pr2ᵉ has-top-element-Finitely-Graded-Poset-Propᵉ =
    is-prop-has-top-element-Finitely-Graded-Posetᵉ

  has-bottom-and-top-element-Finitely-Graded-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  has-bottom-and-top-element-Finitely-Graded-Poset-Propᵉ =
    product-Propᵉ
      has-bottom-element-Finitely-Graded-Poset-Propᵉ
      has-top-element-Finitely-Graded-Poset-Propᵉ

  has-bottom-and-top-element-Finitely-Graded-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-bottom-and-top-element-Finitely-Graded-Posetᵉ =
    type-Propᵉ has-bottom-and-top-element-Finitely-Graded-Poset-Propᵉ

  is-prop-has-bottom-and-top-element-Finitely-Graded-Posetᵉ :
    is-propᵉ has-bottom-and-top-element-Finitely-Graded-Posetᵉ
  is-prop-has-bottom-and-top-element-Finitely-Graded-Posetᵉ =
    is-prop-type-Propᵉ has-bottom-and-top-element-Finitely-Graded-Poset-Propᵉ
```

## Finitely graded subposets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ)
  (Sᵉ : {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Finitely-Graded-Posetᵉ Xᵉ iᵉ → Propᵉ l3ᵉ)
  where

  module _
    (iᵉ : Finᵉ (succ-ℕᵉ kᵉ))
    where

    face-set-Finitely-Graded-Subposetᵉ : Setᵉ (l1ᵉ ⊔ l3ᵉ)
    face-set-Finitely-Graded-Subposetᵉ =
      Σ-Setᵉ
        ( face-Finitely-Graded-Poset-Setᵉ Xᵉ iᵉ)
        ( λ xᵉ → set-Propᵉ (Sᵉ xᵉ))

    face-Finitely-Graded-Subposetᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
    face-Finitely-Graded-Subposetᵉ = type-Setᵉ face-set-Finitely-Graded-Subposetᵉ

    is-set-face-Finitely-Graded-Subposetᵉ : is-setᵉ face-Finitely-Graded-Subposetᵉ
    is-set-face-Finitely-Graded-Subposetᵉ =
      is-set-type-Setᵉ face-set-Finitely-Graded-Subposetᵉ

    eq-face-Finitely-Graded-Subposetᵉ :
      (xᵉ yᵉ : face-Finitely-Graded-Subposetᵉ) → Idᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ) → Idᵉ xᵉ yᵉ
    eq-face-Finitely-Graded-Subposetᵉ xᵉ yᵉ = eq-type-subtypeᵉ Sᵉ

    emb-face-Finitely-Graded-Subposetᵉ :
      face-Finitely-Graded-Subposetᵉ ↪ᵉ face-Finitely-Graded-Posetᵉ Xᵉ iᵉ
    emb-face-Finitely-Graded-Subposetᵉ = emb-subtypeᵉ Sᵉ

    map-emb-face-Finitely-Graded-Subposetᵉ :
      face-Finitely-Graded-Subposetᵉ → face-Finitely-Graded-Posetᵉ Xᵉ iᵉ
    map-emb-face-Finitely-Graded-Subposetᵉ =
      map-embᵉ emb-face-Finitely-Graded-Subposetᵉ

    is-emb-map-emb-face-Finitely-Graded-Subposetᵉ :
      is-embᵉ map-emb-face-Finitely-Graded-Subposetᵉ
    is-emb-map-emb-face-Finitely-Graded-Subposetᵉ =
      is-emb-map-embᵉ emb-face-Finitely-Graded-Subposetᵉ

  module _
    (iᵉ : Finᵉ kᵉ) (yᵉ : face-Finitely-Graded-Subposetᵉ (inl-Finᵉ kᵉ iᵉ))
    (zᵉ : face-Finitely-Graded-Subposetᵉ (succ-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ iᵉ)))
    where

    adjacent-Finitely-Graded-subPoset-Propᵉ : Propᵉ l2ᵉ
    adjacent-Finitely-Graded-subPoset-Propᵉ =
      adjacent-Finitely-Graded-Poset-Propᵉ Xᵉ iᵉ (pr1ᵉ yᵉ) (pr1ᵉ zᵉ)

    adjacent-Finitely-Graded-Subposetᵉ : UUᵉ l2ᵉ
    adjacent-Finitely-Graded-Subposetᵉ =
      type-Propᵉ adjacent-Finitely-Graded-subPoset-Propᵉ

    is-prop-adjacent-Finitely-Graded-Subposetᵉ :
      is-propᵉ adjacent-Finitely-Graded-Subposetᵉ
    is-prop-adjacent-Finitely-Graded-Subposetᵉ =
      is-prop-type-Propᵉ adjacent-Finitely-Graded-subPoset-Propᵉ

  element-set-Finitely-Graded-Subposetᵉ : Setᵉ (l1ᵉ ⊔ l3ᵉ)
  element-set-Finitely-Graded-Subposetᵉ =
    Σ-Setᵉ (Fin-Setᵉ (succ-ℕᵉ kᵉ)) face-set-Finitely-Graded-Subposetᵉ

  type-Finitely-Graded-Subposetᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  type-Finitely-Graded-Subposetᵉ =
    type-Setᵉ element-set-Finitely-Graded-Subposetᵉ

  emb-type-Finitely-Graded-Subposetᵉ :
    type-Finitely-Graded-Subposetᵉ ↪ᵉ type-Finitely-Graded-Posetᵉ Xᵉ
  emb-type-Finitely-Graded-Subposetᵉ =
    emb-totᵉ emb-face-Finitely-Graded-Subposetᵉ

  map-emb-type-Finitely-Graded-Subposetᵉ :
    type-Finitely-Graded-Subposetᵉ → type-Finitely-Graded-Posetᵉ Xᵉ
  map-emb-type-Finitely-Graded-Subposetᵉ =
    map-embᵉ emb-type-Finitely-Graded-Subposetᵉ

  is-emb-map-emb-type-Finitely-Graded-Subposetᵉ :
    is-embᵉ map-emb-type-Finitely-Graded-Subposetᵉ
  is-emb-map-emb-type-Finitely-Graded-Subposetᵉ =
    is-emb-map-embᵉ emb-type-Finitely-Graded-Subposetᵉ

  is-injective-map-emb-type-Finitely-Graded-Subposetᵉ :
    is-injectiveᵉ map-emb-type-Finitely-Graded-Subposetᵉ
  is-injective-map-emb-type-Finitely-Graded-Subposetᵉ =
    is-injective-is-embᵉ is-emb-map-emb-type-Finitely-Graded-Subposetᵉ

  is-set-type-Finitely-Graded-Subposetᵉ :
    is-setᵉ type-Finitely-Graded-Subposetᵉ
  is-set-type-Finitely-Graded-Subposetᵉ =
    is-set-type-Setᵉ element-set-Finitely-Graded-Subposetᵉ

  leq-Finitely-Graded-Subposet-Propᵉ :
    (xᵉ yᵉ : type-Finitely-Graded-Subposetᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  leq-Finitely-Graded-Subposet-Propᵉ xᵉ yᵉ =
    leq-Finitely-Graded-Poset-Propᵉ Xᵉ
      ( map-emb-type-Finitely-Graded-Subposetᵉ xᵉ)
      ( map-emb-type-Finitely-Graded-Subposetᵉ yᵉ)

  leq-Finitely-Graded-Subposetᵉ :
    (xᵉ yᵉ : type-Finitely-Graded-Subposetᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  leq-Finitely-Graded-Subposetᵉ xᵉ yᵉ =
    type-Propᵉ (leq-Finitely-Graded-Subposet-Propᵉ xᵉ yᵉ)

  is-prop-leq-Finitely-Graded-Subposetᵉ :
    (xᵉ yᵉ : type-Finitely-Graded-Subposetᵉ) →
    is-propᵉ (leq-Finitely-Graded-Subposetᵉ xᵉ yᵉ)
  is-prop-leq-Finitely-Graded-Subposetᵉ xᵉ yᵉ =
    is-prop-type-Propᵉ (leq-Finitely-Graded-Subposet-Propᵉ xᵉ yᵉ)

  refl-leq-Finitely-Graded-Subposetᵉ :
    (xᵉ : type-Finitely-Graded-Subposetᵉ) → leq-Finitely-Graded-Subposetᵉ xᵉ xᵉ
  refl-leq-Finitely-Graded-Subposetᵉ xᵉ =
    refl-leq-Finitely-Graded-Posetᵉ Xᵉ
      ( map-emb-type-Finitely-Graded-Subposetᵉ xᵉ)

  transitive-leq-Finitely-Graded-Subposetᵉ :
    (xᵉ yᵉ zᵉ : type-Finitely-Graded-Subposetᵉ) →
    leq-Finitely-Graded-Subposetᵉ yᵉ zᵉ → leq-Finitely-Graded-Subposetᵉ xᵉ yᵉ →
    leq-Finitely-Graded-Subposetᵉ xᵉ zᵉ
  transitive-leq-Finitely-Graded-Subposetᵉ xᵉ yᵉ zᵉ =
    transitive-leq-Finitely-Graded-Posetᵉ Xᵉ
      ( map-emb-type-Finitely-Graded-Subposetᵉ xᵉ)
      ( map-emb-type-Finitely-Graded-Subposetᵉ yᵉ)
      ( map-emb-type-Finitely-Graded-Subposetᵉ zᵉ)

  antisymmetric-leq-Finitely-Graded-Subposetᵉ :
    (xᵉ yᵉ : type-Finitely-Graded-Subposetᵉ) →
    leq-Finitely-Graded-Subposetᵉ xᵉ yᵉ → leq-Finitely-Graded-Subposetᵉ yᵉ xᵉ → Idᵉ xᵉ yᵉ
  antisymmetric-leq-Finitely-Graded-Subposetᵉ xᵉ yᵉ Hᵉ Kᵉ =
    is-injective-map-emb-type-Finitely-Graded-Subposetᵉ
      ( antisymmetric-leq-Finitely-Graded-Posetᵉ Xᵉ
        ( map-emb-type-Finitely-Graded-Subposetᵉ xᵉ)
        ( map-emb-type-Finitely-Graded-Subposetᵉ yᵉ)
        ( Hᵉ)
        ( Kᵉ))

  preorder-Finitely-Graded-Subposetᵉ : Preorderᵉ (l1ᵉ ⊔ l3ᵉ) (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ preorder-Finitely-Graded-Subposetᵉ =
    type-Finitely-Graded-Subposetᵉ
  pr1ᵉ (pr2ᵉ preorder-Finitely-Graded-Subposetᵉ) =
    leq-Finitely-Graded-Subposet-Propᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ preorder-Finitely-Graded-Subposetᵉ)) =
    refl-leq-Finitely-Graded-Subposetᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ preorder-Finitely-Graded-Subposetᵉ)) =
    transitive-leq-Finitely-Graded-Subposetᵉ

  poset-Finitely-Graded-Subposetᵉ : Posetᵉ (l1ᵉ ⊔ l3ᵉ) (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ poset-Finitely-Graded-Subposetᵉ =
    preorder-Finitely-Graded-Subposetᵉ
  pr2ᵉ poset-Finitely-Graded-Subposetᵉ =
    antisymmetric-leq-Finitely-Graded-Subposetᵉ
```

### Inclusion of finitely graded subposets

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ)
  where

  module _
    {l3ᵉ l4ᵉ : Level}
    (Sᵉ : {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Finitely-Graded-Posetᵉ Xᵉ iᵉ → Propᵉ l3ᵉ)
    (Tᵉ : {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Finitely-Graded-Posetᵉ Xᵉ iᵉ → Propᵉ l4ᵉ)
    where

    inclusion-Finitely-Graded-Subposet-Propᵉ : Propᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    inclusion-Finitely-Graded-Subposet-Propᵉ =
      Π-Propᵉ
        ( Finᵉ (succ-ℕᵉ kᵉ))
        ( λ iᵉ →
          Π-Propᵉ
            ( face-Finitely-Graded-Posetᵉ Xᵉ iᵉ)
            ( λ xᵉ → hom-Propᵉ (Sᵉ xᵉ) (Tᵉ xᵉ)))

    inclusion-Finitely-Graded-Subposetᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    inclusion-Finitely-Graded-Subposetᵉ =
      type-Propᵉ inclusion-Finitely-Graded-Subposet-Propᵉ

    is-prop-inclusion-Finitely-Graded-Subposetᵉ :
      is-propᵉ inclusion-Finitely-Graded-Subposetᵉ
    is-prop-inclusion-Finitely-Graded-Subposetᵉ =
      is-prop-type-Propᵉ inclusion-Finitely-Graded-Subposet-Propᵉ

  refl-inclusion-Finitely-Graded-Subposetᵉ :
    {l3ᵉ : Level}
    (Sᵉ : {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Finitely-Graded-Posetᵉ Xᵉ iᵉ → Propᵉ l3ᵉ) →
    inclusion-Finitely-Graded-Subposetᵉ Sᵉ Sᵉ
  refl-inclusion-Finitely-Graded-Subposetᵉ Sᵉ iᵉ xᵉ = idᵉ

  transitive-inclusion-Finitely-Graded-Subposetᵉ :
    {l3ᵉ l4ᵉ l5ᵉ : Level}
    (Sᵉ : {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Finitely-Graded-Posetᵉ Xᵉ iᵉ → Propᵉ l3ᵉ)
    (Tᵉ : {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Finitely-Graded-Posetᵉ Xᵉ iᵉ → Propᵉ l4ᵉ)
    (Uᵉ : {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Finitely-Graded-Posetᵉ Xᵉ iᵉ → Propᵉ l5ᵉ) →
    inclusion-Finitely-Graded-Subposetᵉ Tᵉ Uᵉ →
    inclusion-Finitely-Graded-Subposetᵉ Sᵉ Tᵉ →
    inclusion-Finitely-Graded-Subposetᵉ Sᵉ Uᵉ
  transitive-inclusion-Finitely-Graded-Subposetᵉ Sᵉ Tᵉ Uᵉ gᵉ fᵉ iᵉ xᵉ =
    (gᵉ iᵉ xᵉ) ∘ᵉ (fᵉ iᵉ xᵉ)

  Finitely-Graded-subposet-Preorderᵉ :
    (lᵉ : Level) → Preorderᵉ (l1ᵉ ⊔ lsuc lᵉ) (l1ᵉ ⊔ lᵉ)
  pr1ᵉ (Finitely-Graded-subposet-Preorderᵉ lᵉ) =
    {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Finitely-Graded-Posetᵉ Xᵉ iᵉ → Propᵉ lᵉ
  pr1ᵉ (pr2ᵉ (Finitely-Graded-subposet-Preorderᵉ lᵉ)) =
    inclusion-Finitely-Graded-Subposet-Propᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (Finitely-Graded-subposet-Preorderᵉ lᵉ))) =
    refl-inclusion-Finitely-Graded-Subposetᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (Finitely-Graded-subposet-Preorderᵉ lᵉ))) =
    transitive-inclusion-Finitely-Graded-Subposetᵉ
```

### Chains in finitely graded posets

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ)
  where

  module _
    {l3ᵉ : Level}
    (Sᵉ : {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Finitely-Graded-Posetᵉ Xᵉ iᵉ → Propᵉ l3ᵉ)
    where

    is-chain-Finitely-Graded-Subposet-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
    is-chain-Finitely-Graded-Subposet-Propᵉ =
      is-total-Poset-Propᵉ (poset-Finitely-Graded-Subposetᵉ Xᵉ Sᵉ)

    is-chain-Finitely-Graded-Subposetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
    is-chain-Finitely-Graded-Subposetᵉ =
      type-Propᵉ is-chain-Finitely-Graded-Subposet-Propᵉ

    is-prop-is-chain-Finitely-Graded-Subposetᵉ :
      is-propᵉ is-chain-Finitely-Graded-Subposetᵉ
    is-prop-is-chain-Finitely-Graded-Subposetᵉ =
      is-prop-type-Propᵉ is-chain-Finitely-Graded-Subposet-Propᵉ

  chain-Finitely-Graded-Posetᵉ : (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
  chain-Finitely-Graded-Posetᵉ lᵉ = Σᵉ _ (is-chain-Finitely-Graded-Subposetᵉ {lᵉ})

  module _
    {lᵉ : Level} (Cᵉ : chain-Finitely-Graded-Posetᵉ lᵉ)
    where

    subtype-chain-Finitely-Graded-Posetᵉ :
      {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Finitely-Graded-Posetᵉ Xᵉ iᵉ → Propᵉ lᵉ
    subtype-chain-Finitely-Graded-Posetᵉ = pr1ᵉ Cᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ)
  (Cᵉ : chain-Finitely-Graded-Posetᵉ Xᵉ l3ᵉ) (Dᵉ : chain-Finitely-Graded-Posetᵉ Xᵉ l4ᵉ)
  where

  inclusion-chain-Finitely-Graded-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  inclusion-chain-Finitely-Graded-Poset-Propᵉ =
    inclusion-Finitely-Graded-Subposet-Propᵉ Xᵉ
      ( subtype-chain-Finitely-Graded-Posetᵉ Xᵉ Cᵉ)
      ( subtype-chain-Finitely-Graded-Posetᵉ Xᵉ Dᵉ)

  inclusion-chain-Finitely-Graded-Posetᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  inclusion-chain-Finitely-Graded-Posetᵉ =
    inclusion-Finitely-Graded-Subposetᵉ Xᵉ
      ( subtype-chain-Finitely-Graded-Posetᵉ Xᵉ Cᵉ)
      ( subtype-chain-Finitely-Graded-Posetᵉ Xᵉ Dᵉ)

  is-prop-inclusion-chain-Finitely-Graded-Posetᵉ :
    is-propᵉ inclusion-chain-Finitely-Graded-Posetᵉ
  is-prop-inclusion-chain-Finitely-Graded-Posetᵉ =
    is-prop-inclusion-Finitely-Graded-Subposetᵉ Xᵉ
      ( subtype-chain-Finitely-Graded-Posetᵉ Xᵉ Cᵉ)
      ( subtype-chain-Finitely-Graded-Posetᵉ Xᵉ Dᵉ)
```

### Maximal chains in preorders

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : ℕᵉ} (Xᵉ : Finitely-Graded-Posetᵉ l1ᵉ l2ᵉ kᵉ)
  where

  module _
    {l3ᵉ : Level} (Cᵉ : chain-Finitely-Graded-Posetᵉ Xᵉ l3ᵉ)
    where

    is-maximal-chain-Finitely-Graded-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
    is-maximal-chain-Finitely-Graded-Poset-Propᵉ =
      Π-Propᵉ
        ( chain-Finitely-Graded-Posetᵉ Xᵉ l3ᵉ)
        ( λ Dᵉ → inclusion-chain-Finitely-Graded-Poset-Propᵉ Xᵉ Dᵉ Cᵉ)

    is-maximal-chain-Finitely-Graded-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
    is-maximal-chain-Finitely-Graded-Posetᵉ =
      type-Propᵉ is-maximal-chain-Finitely-Graded-Poset-Propᵉ

    is-prop-is-maximal-chain-Finitely-Graded-Posetᵉ :
      is-propᵉ is-maximal-chain-Finitely-Graded-Posetᵉ
    is-prop-is-maximal-chain-Finitely-Graded-Posetᵉ =
      is-prop-type-Propᵉ is-maximal-chain-Finitely-Graded-Poset-Propᵉ

  maximal-chain-Finitely-Graded-Posetᵉ :
    (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
  maximal-chain-Finitely-Graded-Posetᵉ lᵉ =
    Σᵉ _ (is-maximal-chain-Finitely-Graded-Posetᵉ {lᵉ})

  module _
    {l3ᵉ : Level} (Cᵉ : maximal-chain-Finitely-Graded-Posetᵉ l3ᵉ)
    where

    chain-maximal-chain-Finitely-Graded-Posetᵉ :
      chain-Finitely-Graded-Posetᵉ Xᵉ l3ᵉ
    chain-maximal-chain-Finitely-Graded-Posetᵉ = pr1ᵉ Cᵉ

    is-maximal-chain-maximal-chain-Finitely-Graded-Posetᵉ :
      is-maximal-chain-Finitely-Graded-Posetᵉ
        chain-maximal-chain-Finitely-Graded-Posetᵉ
    is-maximal-chain-maximal-chain-Finitely-Graded-Posetᵉ = pr2ᵉ Cᵉ

    subtype-maximal-chain-Finitely-Graded-Posetᵉ :
      {iᵉ : Finᵉ (succ-ℕᵉ kᵉ)} → face-Finitely-Graded-Posetᵉ Xᵉ iᵉ → Propᵉ l3ᵉ
    subtype-maximal-chain-Finitely-Graded-Posetᵉ =
      subtype-chain-Finitely-Graded-Posetᵉ Xᵉ
        chain-maximal-chain-Finitely-Graded-Posetᵉ
```