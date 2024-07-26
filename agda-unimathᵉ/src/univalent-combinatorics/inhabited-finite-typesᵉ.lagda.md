# Inhabited finite types

```agda
module univalent-combinatorics.inhabited-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.subuniversesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Anᵉ **inhabitedᵉ finiteᵉ type**ᵉ isᵉ aᵉ
[finiteᵉ type](univalent-combinatorics.finite-types.mdᵉ) thatᵉ isᵉ
[inhabited](foundation.inhabited-types.md),ᵉ meaningᵉ itᵉ isᵉ aᵉ typeᵉ thatᵉ isᵉ
[merelyᵉ equivalent](foundation.mere-equivalences.mdᵉ) to aᵉ
[standardᵉ finiteᵉ type](univalent-combinatorics.standard-finite-types.md),ᵉ andᵉ
thatᵉ comesᵉ equippedᵉ with aᵉ termᵉ ofᵉ itsᵉ
[propositionalᵉ truncation](foundation.propositional-truncations.md).ᵉ

## Definitions

### Inhabited finite types

```agda
Inhabited-𝔽ᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Inhabited-𝔽ᵉ lᵉ = Σᵉ (𝔽ᵉ lᵉ) (λ Xᵉ → is-inhabitedᵉ (type-𝔽ᵉ Xᵉ))

module _
  {lᵉ : Level} (Xᵉ : Inhabited-𝔽ᵉ lᵉ)
  where

  finite-type-Inhabited-𝔽ᵉ : 𝔽ᵉ lᵉ
  finite-type-Inhabited-𝔽ᵉ = pr1ᵉ Xᵉ

  type-Inhabited-𝔽ᵉ : UUᵉ lᵉ
  type-Inhabited-𝔽ᵉ = type-𝔽ᵉ finite-type-Inhabited-𝔽ᵉ

  is-finite-Inhabited-𝔽ᵉ : is-finiteᵉ type-Inhabited-𝔽ᵉ
  is-finite-Inhabited-𝔽ᵉ = is-finite-type-𝔽ᵉ finite-type-Inhabited-𝔽ᵉ

  is-inhabited-type-Inhabited-𝔽ᵉ : is-inhabitedᵉ type-Inhabited-𝔽ᵉ
  is-inhabited-type-Inhabited-𝔽ᵉ = pr2ᵉ Xᵉ

  inhabited-type-Inhabited-𝔽ᵉ : Inhabited-Typeᵉ lᵉ
  pr1ᵉ inhabited-type-Inhabited-𝔽ᵉ = type-Inhabited-𝔽ᵉ
  pr2ᵉ inhabited-type-Inhabited-𝔽ᵉ = is-inhabited-type-Inhabited-𝔽ᵉ

compute-Inhabited-𝔽ᵉ :
  {lᵉ : Level} →
  Inhabited-𝔽ᵉ lᵉ ≃ᵉ
  Σᵉ (Inhabited-Typeᵉ lᵉ) (λ Xᵉ → is-finiteᵉ (type-Inhabited-Typeᵉ Xᵉ))
compute-Inhabited-𝔽ᵉ = equiv-right-swap-Σᵉ

is-finite-and-inhabited-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
is-finite-and-inhabited-Propᵉ Xᵉ =
  product-Propᵉ (is-finite-Propᵉ Xᵉ) (is-inhabited-Propᵉ Xᵉ)

is-finite-and-inhabitedᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-finite-and-inhabitedᵉ Xᵉ =
  type-Propᵉ (is-finite-and-inhabited-Propᵉ Xᵉ)

compute-Inhabited-𝔽'ᵉ :
  {lᵉ : Level} →
  Inhabited-𝔽ᵉ lᵉ ≃ᵉ type-subuniverseᵉ is-finite-and-inhabited-Propᵉ
compute-Inhabited-𝔽'ᵉ = associative-Σᵉ _ _ _

map-compute-Inhabited-𝔽'ᵉ :
  {lᵉ : Level} →
  Inhabited-𝔽ᵉ lᵉ → type-subuniverseᵉ is-finite-and-inhabited-Propᵉ
map-compute-Inhabited-𝔽'ᵉ = map-associative-Σᵉ _ _ _

map-inv-compute-Inhabited-𝔽'ᵉ :
  {lᵉ : Level} →
  type-subuniverseᵉ is-finite-and-inhabited-Propᵉ → Inhabited-𝔽ᵉ lᵉ
map-inv-compute-Inhabited-𝔽'ᵉ = map-inv-associative-Σᵉ _ _ _
```

### Families of inhabited types

```agda
Fam-Inhabited-Types-𝔽ᵉ :
  {l1ᵉ : Level} → (l2ᵉ : Level) → (Xᵉ : 𝔽ᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Fam-Inhabited-Types-𝔽ᵉ l2ᵉ Xᵉ = type-𝔽ᵉ Xᵉ → Inhabited-𝔽ᵉ l2ᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Yᵉ : Fam-Inhabited-Types-𝔽ᵉ l2ᵉ Xᵉ)
  where

  type-Fam-Inhabited-Types-𝔽ᵉ : type-𝔽ᵉ Xᵉ → UUᵉ l2ᵉ
  type-Fam-Inhabited-Types-𝔽ᵉ xᵉ = type-Inhabited-𝔽ᵉ (Yᵉ xᵉ)

  finite-type-Fam-Inhabited-Types-𝔽ᵉ : type-𝔽ᵉ Xᵉ → 𝔽ᵉ l2ᵉ
  pr1ᵉ (finite-type-Fam-Inhabited-Types-𝔽ᵉ xᵉ) = type-Fam-Inhabited-Types-𝔽ᵉ xᵉ
  pr2ᵉ (finite-type-Fam-Inhabited-Types-𝔽ᵉ xᵉ) = is-finite-Inhabited-𝔽ᵉ (Yᵉ xᵉ)

  is-inhabited-type-Fam-Inhabited-Types-𝔽ᵉ :
    (xᵉ : type-𝔽ᵉ Xᵉ) → is-inhabitedᵉ (type-Fam-Inhabited-Types-𝔽ᵉ xᵉ)
  is-inhabited-type-Fam-Inhabited-Types-𝔽ᵉ xᵉ =
    is-inhabited-type-Inhabited-𝔽ᵉ (Yᵉ xᵉ)

  total-Fam-Inhabited-Types-𝔽ᵉ : 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  total-Fam-Inhabited-Types-𝔽ᵉ = Σ-𝔽ᵉ Xᵉ finite-type-Fam-Inhabited-Types-𝔽ᵉ

compute-Fam-Inhabited-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} → (Xᵉ : 𝔽ᵉ l1ᵉ) →
  Fam-Inhabited-Types-𝔽ᵉ l2ᵉ Xᵉ ≃ᵉ
  Σᵉ ( Fam-Inhabited-Typesᵉ l2ᵉ (type-𝔽ᵉ Xᵉ))
    ( λ Yᵉ → (xᵉ : type-𝔽ᵉ Xᵉ) → is-finiteᵉ (type-Inhabited-Typeᵉ (Yᵉ xᵉ)))
compute-Fam-Inhabited-𝔽ᵉ Xᵉ =
  ( distributive-Π-Σᵉ) ∘eᵉ
  ( equiv-Πᵉ
    ( λ _ → Σᵉ (Inhabited-Typeᵉ _) (is-finiteᵉ ∘ᵉ type-Inhabited-Typeᵉ))
    ( id-equivᵉ)
    ( λ _ → compute-Inhabited-𝔽ᵉ))
```

## Proposition

### Equality in inhabited finite types

```agda
eq-equiv-Inhabited-𝔽ᵉ :
  {lᵉ : Level} → (Xᵉ Yᵉ : Inhabited-𝔽ᵉ lᵉ) →
  type-Inhabited-𝔽ᵉ Xᵉ ≃ᵉ type-Inhabited-𝔽ᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
eq-equiv-Inhabited-𝔽ᵉ Xᵉ Yᵉ eᵉ =
  eq-type-subtypeᵉ
    ( λ Xᵉ → is-inhabited-Propᵉ (type-𝔽ᵉ Xᵉ))
    ( eq-equiv-𝔽ᵉ
      ( finite-type-Inhabited-𝔽ᵉ Xᵉ)
      ( finite-type-Inhabited-𝔽ᵉ Yᵉ)
      ( eᵉ))
```

### Every type in `UU-Fin (succ-ℕ n)` is an inhabited finite type

```agda
is-finite-and-inhabited-type-UU-Fin-succ-ℕᵉ :
  {lᵉ : Level} → (nᵉ : ℕᵉ) → (Fᵉ : UU-Finᵉ lᵉ (succ-ℕᵉ nᵉ)) →
  is-finite-and-inhabitedᵉ (type-UU-Finᵉ (succ-ℕᵉ nᵉ) Fᵉ)
pr1ᵉ (is-finite-and-inhabited-type-UU-Fin-succ-ℕᵉ nᵉ Fᵉ) =
  is-finite-type-UU-Finᵉ (succ-ℕᵉ nᵉ) Fᵉ
pr2ᵉ (is-finite-and-inhabited-type-UU-Fin-succ-ℕᵉ nᵉ Fᵉ) =
  is-inhabited-type-UU-Fin-succ-ℕᵉ nᵉ Fᵉ
```