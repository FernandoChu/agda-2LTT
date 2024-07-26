# Inhabited types

```agda
module foundation.inhabited-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

**Inhabitedᵉ types**ᵉ areᵉ typesᵉ equippedᵉ with anᵉ elementᵉ ofᵉ itsᵉ propositionalᵉ
truncation.ᵉ

**Remark:**ᵉ Thisᵉ contrastsᵉ with theᵉ definitionᵉ ofᵉ
[pointedᵉ types](structured-types.pointed-types.mdᵉ) in thatᵉ weᵉ do notᵉ discernᵉ
betweenᵉ proofsᵉ ofᵉ inhabitedness,ᵉ soᵉ thatᵉ itᵉ isᵉ merelyᵉ aᵉ propertyᵉ ofᵉ theᵉ typeᵉ to
beᵉ inhabited.ᵉ

## Definitions

### Inhabited types

```agda
is-inhabited-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
is-inhabited-Propᵉ Xᵉ = trunc-Propᵉ Xᵉ

is-inhabitedᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-inhabitedᵉ Xᵉ = type-Propᵉ (is-inhabited-Propᵉ Xᵉ)

is-property-is-inhabitedᵉ : {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-propᵉ (is-inhabitedᵉ Xᵉ)
is-property-is-inhabitedᵉ Xᵉ = is-prop-type-Propᵉ (is-inhabited-Propᵉ Xᵉ)

Inhabited-Typeᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Inhabited-Typeᵉ lᵉ = Σᵉ (UUᵉ lᵉ) is-inhabitedᵉ

module _
  {lᵉ : Level} (Xᵉ : Inhabited-Typeᵉ lᵉ)
  where

  type-Inhabited-Typeᵉ : UUᵉ lᵉ
  type-Inhabited-Typeᵉ = pr1ᵉ Xᵉ

  is-inhabited-type-Inhabited-Typeᵉ : type-trunc-Propᵉ type-Inhabited-Typeᵉ
  is-inhabited-type-Inhabited-Typeᵉ = pr2ᵉ Xᵉ
```

### Families of inhabited types

```agda
Fam-Inhabited-Typesᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Fam-Inhabited-Typesᵉ l2ᵉ Xᵉ = Xᵉ → Inhabited-Typeᵉ l2ᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Yᵉ : Fam-Inhabited-Typesᵉ l2ᵉ Xᵉ)
  where

  type-Fam-Inhabited-Typesᵉ : Xᵉ → UUᵉ l2ᵉ
  type-Fam-Inhabited-Typesᵉ xᵉ = type-Inhabited-Typeᵉ (Yᵉ xᵉ)

  is-inhabited-type-Fam-Inhabited-Typesᵉ :
    (xᵉ : Xᵉ) → type-trunc-Propᵉ (type-Fam-Inhabited-Typesᵉ xᵉ)
  is-inhabited-type-Fam-Inhabited-Typesᵉ xᵉ =
    is-inhabited-type-Inhabited-Typeᵉ (Yᵉ xᵉ)

  total-Fam-Inhabited-Typesᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  total-Fam-Inhabited-Typesᵉ = Σᵉ Xᵉ type-Fam-Inhabited-Typesᵉ
```

## Properties

### Characterization of equality of inhabited types

```agda
equiv-Inhabited-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} → Inhabited-Typeᵉ l1ᵉ → Inhabited-Typeᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
equiv-Inhabited-Typeᵉ Xᵉ Yᵉ = type-Inhabited-Typeᵉ Xᵉ ≃ᵉ type-Inhabited-Typeᵉ Yᵉ

module _
  {lᵉ : Level} (Xᵉ : Inhabited-Typeᵉ lᵉ)
  where

  is-torsorial-equiv-Inhabited-Typeᵉ :
    is-torsorialᵉ (equiv-Inhabited-Typeᵉ Xᵉ)
  is-torsorial-equiv-Inhabited-Typeᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-equivᵉ (type-Inhabited-Typeᵉ Xᵉ))
      ( λ Xᵉ → is-prop-type-trunc-Propᵉ)
      ( type-Inhabited-Typeᵉ Xᵉ)
      ( id-equivᵉ)
      ( is-inhabited-type-Inhabited-Typeᵉ Xᵉ)

  equiv-eq-Inhabited-Typeᵉ :
    (Yᵉ : Inhabited-Typeᵉ lᵉ) → (Xᵉ ＝ᵉ Yᵉ) → equiv-Inhabited-Typeᵉ Xᵉ Yᵉ
  equiv-eq-Inhabited-Typeᵉ .Xᵉ reflᵉ = id-equivᵉ

  is-equiv-equiv-eq-Inhabited-Typeᵉ :
    (Yᵉ : Inhabited-Typeᵉ lᵉ) → is-equivᵉ (equiv-eq-Inhabited-Typeᵉ Yᵉ)
  is-equiv-equiv-eq-Inhabited-Typeᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-Inhabited-Typeᵉ
      equiv-eq-Inhabited-Typeᵉ

  extensionality-Inhabited-Typeᵉ :
    (Yᵉ : Inhabited-Typeᵉ lᵉ) → (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-Inhabited-Typeᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-Inhabited-Typeᵉ Yᵉ) = equiv-eq-Inhabited-Typeᵉ Yᵉ
  pr2ᵉ (extensionality-Inhabited-Typeᵉ Yᵉ) = is-equiv-equiv-eq-Inhabited-Typeᵉ Yᵉ

  eq-equiv-Inhabited-Typeᵉ :
    (Yᵉ : Inhabited-Typeᵉ lᵉ) → equiv-Inhabited-Typeᵉ Xᵉ Yᵉ → (Xᵉ ＝ᵉ Yᵉ)
  eq-equiv-Inhabited-Typeᵉ Yᵉ =
    map-inv-equivᵉ (extensionality-Inhabited-Typeᵉ Yᵉ)
```

### Characterization of equality of families of inhabited types

```agda
equiv-Fam-Inhabited-Typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} →
  Fam-Inhabited-Typesᵉ l2ᵉ Xᵉ → Fam-Inhabited-Typesᵉ l3ᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
equiv-Fam-Inhabited-Typesᵉ {Xᵉ = Xᵉ} Yᵉ Zᵉ =
  (xᵉ : Xᵉ) → equiv-Inhabited-Typeᵉ (Yᵉ xᵉ) (Zᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Yᵉ : Fam-Inhabited-Typesᵉ l2ᵉ Xᵉ)
  where

  id-equiv-Fam-Inhabited-Typesᵉ : equiv-Fam-Inhabited-Typesᵉ Yᵉ Yᵉ
  id-equiv-Fam-Inhabited-Typesᵉ = id-equiv-famᵉ (type-Fam-Inhabited-Typesᵉ Yᵉ)

  is-torsorial-equiv-Fam-Inhabited-Typesᵉ :
    is-torsorialᵉ (equiv-Fam-Inhabited-Typesᵉ Yᵉ)
  is-torsorial-equiv-Fam-Inhabited-Typesᵉ =
    is-torsorial-Eq-Πᵉ (λ xᵉ → is-torsorial-equiv-Inhabited-Typeᵉ (Yᵉ xᵉ))

  equiv-eq-Fam-Inhabited-Typesᵉ :
    (Zᵉ : Fam-Inhabited-Typesᵉ l2ᵉ Xᵉ) → (Yᵉ ＝ᵉ Zᵉ) → equiv-Fam-Inhabited-Typesᵉ Yᵉ Zᵉ
  equiv-eq-Fam-Inhabited-Typesᵉ .Yᵉ reflᵉ = id-equiv-Fam-Inhabited-Typesᵉ

  is-equiv-equiv-eq-Fam-Inhabited-Typesᵉ :
    (Zᵉ : Fam-Inhabited-Typesᵉ l2ᵉ Xᵉ) → is-equivᵉ (equiv-eq-Fam-Inhabited-Typesᵉ Zᵉ)
  is-equiv-equiv-eq-Fam-Inhabited-Typesᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-Fam-Inhabited-Typesᵉ
      equiv-eq-Fam-Inhabited-Typesᵉ
```

### Inhabited types are closed under `Σ`

```agda
is-inhabited-Σᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : Xᵉ → UUᵉ l2ᵉ} →
  is-inhabitedᵉ Xᵉ → ((xᵉ : Xᵉ) → is-inhabitedᵉ (Yᵉ xᵉ)) → is-inhabitedᵉ (Σᵉ Xᵉ Yᵉ)
is-inhabited-Σᵉ {l1ᵉ} {l2ᵉ} {Xᵉ} {Yᵉ} Hᵉ Kᵉ =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( is-inhabited-Propᵉ (Σᵉ Xᵉ Yᵉ))
    ( λ xᵉ →
      apply-universal-property-trunc-Propᵉ
        ( Kᵉ xᵉ)
        ( is-inhabited-Propᵉ (Σᵉ Xᵉ Yᵉ))
        ( λ yᵉ → unit-trunc-Propᵉ (xᵉ ,ᵉ yᵉ)))

Σ-Inhabited-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Inhabited-Typeᵉ l1ᵉ)
  (Yᵉ : type-Inhabited-Typeᵉ Xᵉ → Inhabited-Typeᵉ l2ᵉ) → Inhabited-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (Σ-Inhabited-Typeᵉ Xᵉ Yᵉ) =
  Σᵉ (type-Inhabited-Typeᵉ Xᵉ) (λ xᵉ → type-Inhabited-Typeᵉ (Yᵉ xᵉ))
pr2ᵉ (Σ-Inhabited-Typeᵉ Xᵉ Yᵉ) =
  is-inhabited-Σᵉ
    ( is-inhabited-type-Inhabited-Typeᵉ Xᵉ)
    ( λ xᵉ → is-inhabited-type-Inhabited-Typeᵉ (Yᵉ xᵉ))
```

### Inhabited types are closed under maps

```agda
map-is-inhabitedᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (fᵉ : Aᵉ → Bᵉ) → is-inhabitedᵉ Aᵉ → is-inhabitedᵉ Bᵉ
map-is-inhabitedᵉ fᵉ = map-trunc-Propᵉ fᵉ
```

### Contractible types are inhabited

```agda
is-inhabited-is-contrᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-contrᵉ Aᵉ → is-inhabitedᵉ Aᵉ
is-inhabited-is-contrᵉ pᵉ =
  unit-trunc-Propᵉ (centerᵉ pᵉ)
```

### Inhabited propositions are contractible

```agda
is-contr-is-inhabited-is-propᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-propᵉ Aᵉ → is-inhabitedᵉ Aᵉ → is-contrᵉ Aᵉ
is-contr-is-inhabited-is-propᵉ {Aᵉ = Aᵉ} pᵉ hᵉ =
  apply-universal-property-trunc-Propᵉ
    ( hᵉ)
    ( is-contr-Propᵉ Aᵉ)
    ( λ aᵉ → aᵉ ,ᵉ eq-is-prop'ᵉ pᵉ aᵉ)
```

## See also

-ᵉ Theᵉ notionᵉ ofᵉ _nonemptyᵉ typesᵉ_ isᵉ treatedᵉ in
  [`foundation.empty-types`](foundation.empty-types.md).ᵉ Inᵉ particular,ᵉ everyᵉ
  inhabitedᵉ typeᵉ isᵉ nonempty.ᵉ
-ᵉ Forᵉ theᵉ notionᵉ ofᵉ _pointedᵉ types_,ᵉ seeᵉ
  [`structured-types.pointed-types`](structured-types.pointed-types.md).ᵉ