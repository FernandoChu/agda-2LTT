# Ideals of semirings

```agda
module ring-theory.ideals-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.submonoidsᵉ

open import ring-theory.semiringsᵉ
open import ring-theory.subsets-semiringsᵉ
```

</details>

## Idea

Anᵉ **ideal**ᵉ (resp.ᵉ aᵉ **left/rightᵉ ideal**ᵉ) ofᵉ aᵉ semiringᵉ `R`ᵉ isᵉ anᵉ additiveᵉ
submoduleᵉ ofᵉ `R`ᵉ thatᵉ isᵉ closedᵉ underᵉ multiplicationᵉ byᵉ elementsᵉ ofᵉ `R`ᵉ (fromᵉ
theᵉ left/right).ᵉ

### Note

Thisᵉ isᵉ theᵉ standardᵉ definitionᵉ ofᵉ idealsᵉ in semirings.ᵉ However,ᵉ suchᵉ two-sidedᵉ
idealsᵉ do notᵉ correspondᵉ uniquelyᵉ to congruencesᵉ onᵉ `R`.ᵉ Ifᵉ weᵉ askᵉ in additionᵉ
thatᵉ theᵉ underlyingᵉ additiveᵉ submoduleᵉ isᵉ normal,ᵉ thenᵉ weᵉ getᵉ uniqueᵉ
correspondenceᵉ to congruences.ᵉ Weᵉ willᵉ callᵉ suchᵉ idealsᵉ **normal**.ᵉ

## Definitions

### Additive submonoids

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ)
  where

  is-additive-submonoid-Semiringᵉ :
    {l2ᵉ : Level} → subset-Semiringᵉ l2ᵉ Rᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-additive-submonoid-Semiringᵉ =
    is-submonoid-subset-Monoidᵉ (additive-monoid-Semiringᵉ Rᵉ)
```

### Left ideals

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ)
  where

  is-left-ideal-subset-Semiringᵉ :
    {l2ᵉ : Level} → subset-Semiringᵉ l2ᵉ Rᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-left-ideal-subset-Semiringᵉ Pᵉ =
    is-additive-submonoid-Semiringᵉ Rᵉ Pᵉ ×ᵉ
    is-closed-under-left-multiplication-subset-Semiringᵉ Rᵉ Pᵉ

left-ideal-Semiringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
left-ideal-Semiringᵉ lᵉ Rᵉ =
  Σᵉ (subset-Semiringᵉ lᵉ Rᵉ) (is-left-ideal-subset-Semiringᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Iᵉ : left-ideal-Semiringᵉ l2ᵉ Rᵉ)
  where

  subset-left-ideal-Semiringᵉ : subset-Semiringᵉ l2ᵉ Rᵉ
  subset-left-ideal-Semiringᵉ = pr1ᵉ Iᵉ

  is-in-left-ideal-Semiringᵉ : type-Semiringᵉ Rᵉ → UUᵉ l2ᵉ
  is-in-left-ideal-Semiringᵉ xᵉ = type-Propᵉ (subset-left-ideal-Semiringᵉ xᵉ)

  type-left-ideal-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-left-ideal-Semiringᵉ = type-subset-Semiringᵉ Rᵉ subset-left-ideal-Semiringᵉ

  inclusion-left-ideal-Semiringᵉ : type-left-ideal-Semiringᵉ → type-Semiringᵉ Rᵉ
  inclusion-left-ideal-Semiringᵉ =
    inclusion-subset-Semiringᵉ Rᵉ subset-left-ideal-Semiringᵉ

  ap-inclusion-left-ideal-Semiringᵉ :
    (xᵉ yᵉ : type-left-ideal-Semiringᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-left-ideal-Semiringᵉ xᵉ ＝ᵉ inclusion-left-ideal-Semiringᵉ yᵉ
  ap-inclusion-left-ideal-Semiringᵉ =
    ap-inclusion-subset-Semiringᵉ Rᵉ subset-left-ideal-Semiringᵉ

  is-in-subset-inclusion-left-ideal-Semiringᵉ :
    (xᵉ : type-left-ideal-Semiringᵉ) →
    is-in-left-ideal-Semiringᵉ (inclusion-left-ideal-Semiringᵉ xᵉ)
  is-in-subset-inclusion-left-ideal-Semiringᵉ =
    is-in-subset-inclusion-subset-Semiringᵉ Rᵉ subset-left-ideal-Semiringᵉ

  is-closed-under-eq-left-ideal-Semiringᵉ :
    {xᵉ yᵉ : type-Semiringᵉ Rᵉ} → is-in-left-ideal-Semiringᵉ xᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-left-ideal-Semiringᵉ yᵉ
  is-closed-under-eq-left-ideal-Semiringᵉ =
    is-closed-under-eq-subset-Semiringᵉ Rᵉ subset-left-ideal-Semiringᵉ

  is-closed-under-eq-left-ideal-Semiring'ᵉ :
    {xᵉ yᵉ : type-Semiringᵉ Rᵉ} → is-in-left-ideal-Semiringᵉ yᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-left-ideal-Semiringᵉ xᵉ
  is-closed-under-eq-left-ideal-Semiring'ᵉ =
    is-closed-under-eq-subset-Semiring'ᵉ Rᵉ subset-left-ideal-Semiringᵉ

  is-left-ideal-subset-left-ideal-Semiringᵉ :
    is-left-ideal-subset-Semiringᵉ Rᵉ subset-left-ideal-Semiringᵉ
  is-left-ideal-subset-left-ideal-Semiringᵉ = pr2ᵉ Iᵉ

  is-additive-submonoid-left-ideal-Semiringᵉ :
    is-additive-submonoid-Semiringᵉ Rᵉ subset-left-ideal-Semiringᵉ
  is-additive-submonoid-left-ideal-Semiringᵉ =
    pr1ᵉ is-left-ideal-subset-left-ideal-Semiringᵉ

  contains-zero-left-ideal-Semiringᵉ :
    is-in-left-ideal-Semiringᵉ (zero-Semiringᵉ Rᵉ)
  contains-zero-left-ideal-Semiringᵉ =
    pr1ᵉ is-additive-submonoid-left-ideal-Semiringᵉ

  is-closed-under-addition-left-ideal-Semiringᵉ :
    is-closed-under-addition-subset-Semiringᵉ Rᵉ subset-left-ideal-Semiringᵉ
  is-closed-under-addition-left-ideal-Semiringᵉ =
    pr2ᵉ is-additive-submonoid-left-ideal-Semiringᵉ

  is-closed-under-left-multiplication-left-ideal-Semiringᵉ :
    is-closed-under-left-multiplication-subset-Semiringᵉ Rᵉ
      subset-left-ideal-Semiringᵉ
  is-closed-under-left-multiplication-left-ideal-Semiringᵉ =
    pr2ᵉ is-left-ideal-subset-left-ideal-Semiringᵉ
```

### Right ideals

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ)
  where

  is-right-ideal-subset-Semiringᵉ :
    {l2ᵉ : Level} → subset-Semiringᵉ l2ᵉ Rᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-right-ideal-subset-Semiringᵉ Pᵉ =
    is-additive-submonoid-Semiringᵉ Rᵉ Pᵉ ×ᵉ
    is-closed-under-right-multiplication-subset-Semiringᵉ Rᵉ Pᵉ

right-ideal-Semiringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
right-ideal-Semiringᵉ lᵉ Rᵉ =
  Σᵉ (subset-Semiringᵉ lᵉ Rᵉ) (is-right-ideal-subset-Semiringᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Iᵉ : right-ideal-Semiringᵉ l2ᵉ Rᵉ)
  where

  subset-right-ideal-Semiringᵉ : subset-Semiringᵉ l2ᵉ Rᵉ
  subset-right-ideal-Semiringᵉ = pr1ᵉ Iᵉ

  is-in-right-ideal-Semiringᵉ : type-Semiringᵉ Rᵉ → UUᵉ l2ᵉ
  is-in-right-ideal-Semiringᵉ xᵉ = type-Propᵉ (subset-right-ideal-Semiringᵉ xᵉ)

  type-right-ideal-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-right-ideal-Semiringᵉ =
    type-subset-Semiringᵉ Rᵉ subset-right-ideal-Semiringᵉ

  inclusion-right-ideal-Semiringᵉ : type-right-ideal-Semiringᵉ → type-Semiringᵉ Rᵉ
  inclusion-right-ideal-Semiringᵉ =
    inclusion-subset-Semiringᵉ Rᵉ subset-right-ideal-Semiringᵉ

  ap-inclusion-right-ideal-Semiringᵉ :
    (xᵉ yᵉ : type-right-ideal-Semiringᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-right-ideal-Semiringᵉ xᵉ ＝ᵉ inclusion-right-ideal-Semiringᵉ yᵉ
  ap-inclusion-right-ideal-Semiringᵉ =
    ap-inclusion-subset-Semiringᵉ Rᵉ subset-right-ideal-Semiringᵉ

  is-in-subset-inclusion-right-ideal-Semiringᵉ :
    (xᵉ : type-right-ideal-Semiringᵉ) →
    is-in-right-ideal-Semiringᵉ (inclusion-right-ideal-Semiringᵉ xᵉ)
  is-in-subset-inclusion-right-ideal-Semiringᵉ =
    is-in-subset-inclusion-subset-Semiringᵉ Rᵉ subset-right-ideal-Semiringᵉ

  is-closed-under-eq-right-ideal-Semiringᵉ :
    {xᵉ yᵉ : type-Semiringᵉ Rᵉ} → is-in-right-ideal-Semiringᵉ xᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-right-ideal-Semiringᵉ yᵉ
  is-closed-under-eq-right-ideal-Semiringᵉ =
    is-closed-under-eq-subset-Semiringᵉ Rᵉ subset-right-ideal-Semiringᵉ

  is-closed-under-eq-right-ideal-Semiring'ᵉ :
    {xᵉ yᵉ : type-Semiringᵉ Rᵉ} → is-in-right-ideal-Semiringᵉ yᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-right-ideal-Semiringᵉ xᵉ
  is-closed-under-eq-right-ideal-Semiring'ᵉ =
    is-closed-under-eq-subset-Semiring'ᵉ Rᵉ subset-right-ideal-Semiringᵉ

  is-right-ideal-subset-right-ideal-Semiringᵉ :
    is-right-ideal-subset-Semiringᵉ Rᵉ subset-right-ideal-Semiringᵉ
  is-right-ideal-subset-right-ideal-Semiringᵉ = pr2ᵉ Iᵉ

  is-additive-submonoid-right-ideal-Semiringᵉ :
    is-additive-submonoid-Semiringᵉ Rᵉ subset-right-ideal-Semiringᵉ
  is-additive-submonoid-right-ideal-Semiringᵉ =
    pr1ᵉ is-right-ideal-subset-right-ideal-Semiringᵉ

  contains-zero-right-ideal-Semiringᵉ :
    is-in-right-ideal-Semiringᵉ (zero-Semiringᵉ Rᵉ)
  contains-zero-right-ideal-Semiringᵉ =
    pr1ᵉ is-additive-submonoid-right-ideal-Semiringᵉ

  is-closed-under-addition-right-ideal-Semiringᵉ :
    is-closed-under-addition-subset-Semiringᵉ Rᵉ subset-right-ideal-Semiringᵉ
  is-closed-under-addition-right-ideal-Semiringᵉ =
    pr2ᵉ is-additive-submonoid-right-ideal-Semiringᵉ

  is-closed-under-right-multiplication-right-ideal-Semiringᵉ :
    is-closed-under-right-multiplication-subset-Semiringᵉ Rᵉ
      subset-right-ideal-Semiringᵉ
  is-closed-under-right-multiplication-right-ideal-Semiringᵉ =
    pr2ᵉ is-right-ideal-subset-right-ideal-Semiringᵉ
```

### Two-sided ideals

```agda
is-ideal-subset-Semiringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Pᵉ : subset-Semiringᵉ l2ᵉ Rᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-ideal-subset-Semiringᵉ Rᵉ Pᵉ =
  is-additive-submonoid-Semiringᵉ Rᵉ Pᵉ ×ᵉ
  ( is-closed-under-left-multiplication-subset-Semiringᵉ Rᵉ Pᵉ ×ᵉ
    is-closed-under-right-multiplication-subset-Semiringᵉ Rᵉ Pᵉ)

ideal-Semiringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
ideal-Semiringᵉ lᵉ Rᵉ =
  Σᵉ (subset-Semiringᵉ lᵉ Rᵉ) (is-ideal-subset-Semiringᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Iᵉ : ideal-Semiringᵉ l2ᵉ Rᵉ)
  where

  subset-ideal-Semiringᵉ : subset-Semiringᵉ l2ᵉ Rᵉ
  subset-ideal-Semiringᵉ = pr1ᵉ Iᵉ

  is-in-ideal-Semiringᵉ : type-Semiringᵉ Rᵉ → UUᵉ l2ᵉ
  is-in-ideal-Semiringᵉ =
    is-in-subset-Semiringᵉ Rᵉ subset-ideal-Semiringᵉ

  is-prop-is-in-ideal-Semiringᵉ :
    (xᵉ : type-Semiringᵉ Rᵉ) → is-propᵉ (is-in-ideal-Semiringᵉ xᵉ)
  is-prop-is-in-ideal-Semiringᵉ =
    is-prop-is-in-subset-Semiringᵉ Rᵉ subset-ideal-Semiringᵉ

  type-ideal-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-ideal-Semiringᵉ =
    type-subset-Semiringᵉ Rᵉ subset-ideal-Semiringᵉ

  inclusion-ideal-Semiringᵉ :
    type-ideal-Semiringᵉ → type-Semiringᵉ Rᵉ
  inclusion-ideal-Semiringᵉ =
    inclusion-subset-Semiringᵉ Rᵉ subset-ideal-Semiringᵉ

  ap-inclusion-ideal-Semiringᵉ :
    (xᵉ yᵉ : type-ideal-Semiringᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-ideal-Semiringᵉ xᵉ ＝ᵉ inclusion-ideal-Semiringᵉ yᵉ
  ap-inclusion-ideal-Semiringᵉ =
    ap-inclusion-subset-Semiringᵉ Rᵉ subset-ideal-Semiringᵉ

  is-in-subset-inclusion-ideal-Semiringᵉ :
    (xᵉ : type-ideal-Semiringᵉ) →
    is-in-ideal-Semiringᵉ (inclusion-ideal-Semiringᵉ xᵉ)
  is-in-subset-inclusion-ideal-Semiringᵉ =
    is-in-subset-inclusion-subset-Semiringᵉ Rᵉ subset-ideal-Semiringᵉ

  is-closed-under-eq-ideal-Semiringᵉ :
    {xᵉ yᵉ : type-Semiringᵉ Rᵉ} → is-in-ideal-Semiringᵉ xᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-ideal-Semiringᵉ yᵉ
  is-closed-under-eq-ideal-Semiringᵉ =
    is-closed-under-eq-subset-Semiringᵉ Rᵉ subset-ideal-Semiringᵉ

  is-closed-under-eq-ideal-Semiring'ᵉ :
    {xᵉ yᵉ : type-Semiringᵉ Rᵉ} → is-in-ideal-Semiringᵉ yᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-ideal-Semiringᵉ xᵉ
  is-closed-under-eq-ideal-Semiring'ᵉ =
    is-closed-under-eq-subset-Semiring'ᵉ Rᵉ subset-ideal-Semiringᵉ

  is-ideal-subset-ideal-Semiringᵉ :
    is-ideal-subset-Semiringᵉ Rᵉ subset-ideal-Semiringᵉ
  is-ideal-subset-ideal-Semiringᵉ = pr2ᵉ Iᵉ

  is-additive-submonoid-ideal-Semiringᵉ :
    is-additive-submonoid-Semiringᵉ Rᵉ subset-ideal-Semiringᵉ
  is-additive-submonoid-ideal-Semiringᵉ =
    pr1ᵉ is-ideal-subset-ideal-Semiringᵉ

  contains-zero-ideal-Semiringᵉ :
    is-in-ideal-Semiringᵉ (zero-Semiringᵉ Rᵉ)
  contains-zero-ideal-Semiringᵉ =
    pr1ᵉ is-additive-submonoid-ideal-Semiringᵉ

  is-closed-under-addition-ideal-Semiringᵉ :
    is-closed-under-addition-subset-Semiringᵉ Rᵉ subset-ideal-Semiringᵉ
  is-closed-under-addition-ideal-Semiringᵉ =
    pr2ᵉ is-additive-submonoid-ideal-Semiringᵉ

  is-closed-under-left-multiplication-ideal-Semiringᵉ :
    is-closed-under-left-multiplication-subset-Semiringᵉ Rᵉ subset-ideal-Semiringᵉ
  is-closed-under-left-multiplication-ideal-Semiringᵉ =
    pr1ᵉ (pr2ᵉ is-ideal-subset-ideal-Semiringᵉ)

  is-closed-under-right-multiplication-ideal-Semiringᵉ :
    is-closed-under-right-multiplication-subset-Semiringᵉ Rᵉ subset-ideal-Semiringᵉ
  is-closed-under-right-multiplication-ideal-Semiringᵉ =
    pr2ᵉ (pr2ᵉ is-ideal-subset-ideal-Semiringᵉ)

  submonoid-ideal-Semiringᵉ : Submonoidᵉ l2ᵉ (additive-monoid-Semiringᵉ Rᵉ)
  pr1ᵉ submonoid-ideal-Semiringᵉ = subset-ideal-Semiringᵉ
  pr1ᵉ (pr2ᵉ submonoid-ideal-Semiringᵉ) = contains-zero-ideal-Semiringᵉ
  pr2ᵉ (pr2ᵉ submonoid-ideal-Semiringᵉ) = is-closed-under-addition-ideal-Semiringᵉ
```