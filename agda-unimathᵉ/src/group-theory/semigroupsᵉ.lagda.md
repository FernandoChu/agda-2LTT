# Semigroups

```agda
module group-theory.semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

**Semigroups**ᵉ areᵉ [sets](foundation-core.sets.mdᵉ) equippedᵉ with anᵉ associativeᵉ
binaryᵉ operation.ᵉ

## Definitions

```agda
has-associative-mulᵉ : {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → UUᵉ lᵉ
has-associative-mulᵉ Xᵉ =
  Σᵉ (Xᵉ → Xᵉ → Xᵉ) (λ μᵉ → (xᵉ yᵉ zᵉ : Xᵉ) → Idᵉ (μᵉ (μᵉ xᵉ yᵉ) zᵉ) (μᵉ xᵉ (μᵉ yᵉ zᵉ)))

has-associative-mul-Setᵉ :
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) → UUᵉ lᵉ
has-associative-mul-Setᵉ Xᵉ =
  has-associative-mulᵉ (type-Setᵉ Xᵉ)

Semigroupᵉ :
  (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Semigroupᵉ lᵉ = Σᵉ (Setᵉ lᵉ) has-associative-mul-Setᵉ

module _
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ)
  where

  set-Semigroupᵉ : Setᵉ lᵉ
  set-Semigroupᵉ = pr1ᵉ Gᵉ

  type-Semigroupᵉ : UUᵉ lᵉ
  type-Semigroupᵉ = type-Setᵉ set-Semigroupᵉ

  is-set-type-Semigroupᵉ : is-setᵉ type-Semigroupᵉ
  is-set-type-Semigroupᵉ = is-set-type-Setᵉ set-Semigroupᵉ

  has-associative-mul-Semigroupᵉ : has-associative-mulᵉ type-Semigroupᵉ
  has-associative-mul-Semigroupᵉ = pr2ᵉ Gᵉ

  mul-Semigroupᵉ : type-Semigroupᵉ → type-Semigroupᵉ → type-Semigroupᵉ
  mul-Semigroupᵉ = pr1ᵉ has-associative-mul-Semigroupᵉ

  mul-Semigroup'ᵉ : type-Semigroupᵉ → type-Semigroupᵉ → type-Semigroupᵉ
  mul-Semigroup'ᵉ xᵉ yᵉ = mul-Semigroupᵉ yᵉ xᵉ

  ap-mul-Semigroupᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Semigroupᵉ} →
    xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → mul-Semigroupᵉ xᵉ yᵉ ＝ᵉ mul-Semigroupᵉ x'ᵉ y'ᵉ
  ap-mul-Semigroupᵉ pᵉ qᵉ = ap-binaryᵉ mul-Semigroupᵉ pᵉ qᵉ

  associative-mul-Semigroupᵉ :
    (xᵉ yᵉ zᵉ : type-Semigroupᵉ) →
    Idᵉ
      ( mul-Semigroupᵉ (mul-Semigroupᵉ xᵉ yᵉ) zᵉ)
      ( mul-Semigroupᵉ xᵉ (mul-Semigroupᵉ yᵉ zᵉ))
  associative-mul-Semigroupᵉ = pr2ᵉ has-associative-mul-Semigroupᵉ

  left-swap-mul-Semigroupᵉ :
    {xᵉ yᵉ zᵉ : type-Semigroupᵉ} → mul-Semigroupᵉ xᵉ yᵉ ＝ᵉ mul-Semigroupᵉ yᵉ xᵉ →
    mul-Semigroupᵉ xᵉ (mul-Semigroupᵉ yᵉ zᵉ) ＝ᵉ
    mul-Semigroupᵉ yᵉ (mul-Semigroupᵉ xᵉ zᵉ)
  left-swap-mul-Semigroupᵉ Hᵉ =
    ( invᵉ (associative-mul-Semigroupᵉ _ _ _)) ∙ᵉ
    ( apᵉ (mul-Semigroup'ᵉ _) Hᵉ) ∙ᵉ
    ( associative-mul-Semigroupᵉ _ _ _)

  right-swap-mul-Semigroupᵉ :
    {xᵉ yᵉ zᵉ : type-Semigroupᵉ} → mul-Semigroupᵉ yᵉ zᵉ ＝ᵉ mul-Semigroupᵉ zᵉ yᵉ →
    mul-Semigroupᵉ (mul-Semigroupᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Semigroupᵉ (mul-Semigroupᵉ xᵉ zᵉ) yᵉ
  right-swap-mul-Semigroupᵉ Hᵉ =
    ( associative-mul-Semigroupᵉ _ _ _) ∙ᵉ
    ( apᵉ (mul-Semigroupᵉ _) Hᵉ) ∙ᵉ
    ( invᵉ (associative-mul-Semigroupᵉ _ _ _))

  interchange-mul-mul-Semigroupᵉ :
    {xᵉ yᵉ zᵉ wᵉ : type-Semigroupᵉ} → mul-Semigroupᵉ yᵉ zᵉ ＝ᵉ mul-Semigroupᵉ zᵉ yᵉ →
    mul-Semigroupᵉ (mul-Semigroupᵉ xᵉ yᵉ) (mul-Semigroupᵉ zᵉ wᵉ) ＝ᵉ
    mul-Semigroupᵉ (mul-Semigroupᵉ xᵉ zᵉ) (mul-Semigroupᵉ yᵉ wᵉ)
  interchange-mul-mul-Semigroupᵉ Hᵉ =
    ( associative-mul-Semigroupᵉ _ _ _) ∙ᵉ
    ( apᵉ (mul-Semigroupᵉ _) (left-swap-mul-Semigroupᵉ Hᵉ)) ∙ᵉ
    ( invᵉ (associative-mul-Semigroupᵉ _ _ _))
```

### The structure of a semigroup

```agda
structure-semigroupᵉ :
  {l1ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l1ᵉ
structure-semigroupᵉ Xᵉ =
  Σᵉ (is-setᵉ Xᵉ) (λ pᵉ → has-associative-mul-Setᵉ (Xᵉ ,ᵉ pᵉ))

semigroup-structure-semigroupᵉ :
  {l1ᵉ : Level} → (Xᵉ : UUᵉ l1ᵉ) → structure-semigroupᵉ Xᵉ → Semigroupᵉ l1ᵉ
pr1ᵉ (semigroup-structure-semigroupᵉ Xᵉ (sᵉ ,ᵉ gᵉ)) = Xᵉ ,ᵉ sᵉ
pr2ᵉ (semigroup-structure-semigroupᵉ Xᵉ (sᵉ ,ᵉ gᵉ)) = gᵉ
```