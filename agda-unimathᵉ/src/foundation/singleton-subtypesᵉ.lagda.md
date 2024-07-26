# Singleton subtypes

```agda
module foundation.singleton-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-componentsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.images-subtypesᵉ
open import foundation.inhabited-subtypesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.setsᵉ
open import foundation.singleton-inductionᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ **singletonᵉ subtype**ᵉ ofᵉ aᵉ typeᵉ `X`ᵉ isᵉ aᵉ [subtype](foundation.subtypes.mdᵉ) `P`ᵉ
ofᵉ `X`ᵉ ofᵉ whichᵉ theᵉ underlyingᵉ typeᵉ isᵉ
[contractible](foundation-core.contractible-types.md).ᵉ Inᵉ informalᵉ writing,ᵉ weᵉ
willᵉ writeᵉ `{x}`ᵉ forᵉ theᵉ **standardᵉ singletonᵉ subtype**ᵉ ofᵉ aᵉ
[set](foundation-core.sets.mdᵉ) `X`ᵉ containingᵉ theᵉ elementᵉ `x`.ᵉ

**Note:**ᵉ Ifᵉ aᵉ subtypeᵉ containingᵉ anᵉ elementᵉ `x`ᵉ isᵉ aᵉ singletonᵉ subtype,ᵉ thenᵉ itᵉ
isᵉ alsoᵉ theᵉ leastᵉ subtypeᵉ containingᵉ `x`.ᵉ However,ᵉ theᵉ reverseᵉ implicationᵉ doesᵉ
notᵉ necessarilyᵉ hold.ᵉ Theᵉ conditionᵉ thatᵉ aᵉ subtypeᵉ isᵉ theᵉ leastᵉ subtypeᵉ
containingᵉ anᵉ elementᵉ `x`ᵉ isᵉ onlyᵉ equivalentᵉ to theᵉ conditionᵉ thatᵉ itsᵉ
underlyingᵉ typeᵉ isᵉ [0-connected](foundation.0-connected-types.md),ᵉ whichᵉ isᵉ aᵉ
weakerᵉ conditionᵉ thanᵉ beingᵉ aᵉ singletonᵉ subtype.ᵉ

## Definitions

### The predicate of being a singleton subtype

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Xᵉ)
  where

  is-singleton-subtype-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-singleton-subtype-Propᵉ = is-contr-Propᵉ (type-subtypeᵉ Pᵉ)

  is-singleton-subtypeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-singleton-subtypeᵉ = type-Propᵉ is-singleton-subtype-Propᵉ

  is-prop-is-singleton-subtypeᵉ :
    is-propᵉ is-singleton-subtypeᵉ
  is-prop-is-singleton-subtypeᵉ = is-prop-type-Propᵉ is-singleton-subtype-Propᵉ
```

### The type of singleton subtypes

```agda
singleton-subtypeᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
singleton-subtypeᵉ l2ᵉ Xᵉ = type-subtypeᵉ (is-singleton-subtype-Propᵉ {l2ᵉ = l2ᵉ} {Xᵉ})

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : singleton-subtypeᵉ l2ᵉ Xᵉ)
  where

  subtype-singleton-subtypeᵉ : subtypeᵉ l2ᵉ Xᵉ
  subtype-singleton-subtypeᵉ = pr1ᵉ Pᵉ

  is-singleton-subtype-singleton-subtypeᵉ :
    is-singleton-subtypeᵉ subtype-singleton-subtypeᵉ
  is-singleton-subtype-singleton-subtypeᵉ = pr2ᵉ Pᵉ
```

### Standard singleton subtypes

```agda
module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) (xᵉ : type-Setᵉ Xᵉ)
  where

  subtype-standard-singleton-subtypeᵉ : subtypeᵉ lᵉ (type-Setᵉ Xᵉ)
  subtype-standard-singleton-subtypeᵉ yᵉ = Id-Propᵉ Xᵉ xᵉ yᵉ

  type-standard-singleton-subtypeᵉ : UUᵉ lᵉ
  type-standard-singleton-subtypeᵉ =
    type-subtypeᵉ subtype-standard-singleton-subtypeᵉ

  inclusion-standard-singleton-subtypeᵉ :
    type-standard-singleton-subtypeᵉ → type-Setᵉ Xᵉ
  inclusion-standard-singleton-subtypeᵉ =
    inclusion-subtypeᵉ subtype-standard-singleton-subtypeᵉ

  standard-singleton-subtypeᵉ : singleton-subtypeᵉ lᵉ (type-Setᵉ Xᵉ)
  pr1ᵉ standard-singleton-subtypeᵉ = subtype-standard-singleton-subtypeᵉ
  pr2ᵉ standard-singleton-subtypeᵉ = is-torsorial-Idᵉ xᵉ

  inhabited-subtype-standard-singleton-subtypeᵉ :
    inhabited-subtypeᵉ lᵉ (type-Setᵉ Xᵉ)
  pr1ᵉ inhabited-subtype-standard-singleton-subtypeᵉ =
    subtype-standard-singleton-subtypeᵉ
  pr2ᵉ inhabited-subtype-standard-singleton-subtypeᵉ =
    unit-trunc-Propᵉ (pairᵉ xᵉ reflᵉ)
```

## Properties

### If a subtype is a singleton subtype containing `x`, then it is the least subtype containing `x`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {xᵉ : Xᵉ} (Pᵉ : subtypeᵉ l2ᵉ Xᵉ) (pᵉ : is-in-subtypeᵉ Pᵉ xᵉ)
  where

  is-least-subtype-containing-element-is-singleton-subtypeᵉ :
    is-singleton-subtypeᵉ Pᵉ → is-least-subtype-containing-elementᵉ xᵉ Pᵉ
  pr1ᵉ (is-least-subtype-containing-element-is-singleton-subtypeᵉ Hᵉ Qᵉ) Lᵉ = Lᵉ xᵉ pᵉ
  pr2ᵉ (is-least-subtype-containing-element-is-singleton-subtypeᵉ Hᵉ Qᵉ) qᵉ yᵉ rᵉ =
    ind-singletonᵉ (xᵉ ,ᵉ pᵉ) Hᵉ (is-in-subtypeᵉ Qᵉ ∘ᵉ pr1ᵉ) qᵉ (yᵉ ,ᵉ rᵉ)
```

### If the identity type `y ↦ x ＝ y` is a subtype, then a subtype containing `x` is a singleton subtype if and only if it is the least subtype containing `x`

**Proof:**ᵉ Weᵉ alreadyᵉ showedᵉ theᵉ forwardᵉ direction.ᵉ Forᵉ theᵉ converse,ᵉ supposeᵉ
thatᵉ theᵉ [identityᵉ type](foundation-core.identity-types.mdᵉ) `yᵉ ↦ᵉ xᵉ ＝ᵉ y`ᵉ isᵉ aᵉ
subtypeᵉ andᵉ thatᵉ `P`ᵉ isᵉ theᵉ leastᵉ subtypeᵉ containingᵉ theᵉ elementᵉ `x`.ᵉ Toᵉ showᵉ
thatᵉ `Σᵉ Xᵉ P`ᵉ isᵉ contractible,ᵉ weᵉ useᵉ theᵉ elementᵉ `(xᵉ ,ᵉ p)`ᵉ asᵉ theᵉ centerᵉ ofᵉ
contraction,ᵉ where `pᵉ : Pᵉ x`ᵉ isᵉ assumed.ᵉ Thenᵉ itᵉ remainsᵉ to constructᵉ theᵉ
contraction.ᵉ Recallᵉ thatᵉ forᵉ anyᵉ elementᵉ `(yᵉ ,ᵉ qᵉ) : Σᵉ Xᵉ P`ᵉ weᵉ haveᵉ aᵉ functionᵉ

```text
  eq-type-subtypeᵉ Pᵉ : (xᵉ ＝ᵉ yᵉ) → ((xᵉ ,ᵉ pᵉ) ＝ᵉ (yᵉ ,ᵉ q)).ᵉ
```

Thereforeᵉ itᵉ sufficesᵉ to showᵉ thatᵉ `xᵉ ＝ᵉ y`.ᵉ Thisᵉ isᵉ aᵉ
[proposition](foundation-core.propositions.md).ᵉ Byᵉ theᵉ assumptionᵉ thatᵉ `P`ᵉ isᵉ
theᵉ leastᵉ subtypeᵉ containingᵉ `x`ᵉ weᵉ haveᵉ aᵉ functionᵉ `Pᵉ uᵉ → xᵉ ＝ᵉ u`ᵉ forᵉ allᵉ `u`,ᵉ
soᵉ `xᵉ ＝ᵉ y`ᵉ follows.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {xᵉ : Xᵉ} (Pᵉ : subtypeᵉ l2ᵉ Xᵉ) (pᵉ : is-in-subtypeᵉ Pᵉ xᵉ)
  where

  is-singleton-subtype-is-least-subtype-containing-elementᵉ :
    (Hᵉ : (yᵉ : Xᵉ) → is-propᵉ (xᵉ ＝ᵉ yᵉ)) →
    is-least-subtype-containing-elementᵉ xᵉ Pᵉ → is-singleton-subtypeᵉ Pᵉ
  pr1ᵉ (is-singleton-subtype-is-least-subtype-containing-elementᵉ Hᵉ Lᵉ) = (xᵉ ,ᵉ pᵉ)
  pr2ᵉ (is-singleton-subtype-is-least-subtype-containing-elementᵉ Hᵉ Lᵉ) (yᵉ ,ᵉ qᵉ) =
    eq-type-subtypeᵉ Pᵉ (backward-implicationᵉ (Lᵉ (λ yᵉ → xᵉ ＝ᵉ yᵉ ,ᵉ Hᵉ yᵉ)) reflᵉ yᵉ qᵉ)

is-singleton-subtype-is-least-subtype-containing-element-Setᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Setᵉ l1ᵉ) {xᵉ : type-Setᵉ Xᵉ} (Pᵉ : subtypeᵉ l2ᵉ (type-Setᵉ Xᵉ))
  (pᵉ : is-in-subtypeᵉ Pᵉ xᵉ) →
  is-least-subtype-containing-elementᵉ xᵉ Pᵉ → is-singleton-subtypeᵉ Pᵉ
is-singleton-subtype-is-least-subtype-containing-element-Setᵉ Xᵉ Pᵉ pᵉ =
  is-singleton-subtype-is-least-subtype-containing-elementᵉ Pᵉ pᵉ
    ( is-set-type-Setᵉ Xᵉ _)
```

### Any two singleton subtypes containing a given element `x` have the same elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {xᵉ : Xᵉ} (Pᵉ : subtypeᵉ l2ᵉ Xᵉ) (Qᵉ : subtypeᵉ l3ᵉ Xᵉ)
  (pᵉ : is-in-subtypeᵉ Pᵉ xᵉ) (qᵉ : is-in-subtypeᵉ Qᵉ xᵉ)
  where

  inclusion-is-singleton-subtypeᵉ :
    is-singleton-subtypeᵉ Pᵉ → Pᵉ ⊆ᵉ Qᵉ
  inclusion-is-singleton-subtypeᵉ sᵉ =
    backward-implicationᵉ
      ( is-least-subtype-containing-element-is-singleton-subtypeᵉ Pᵉ pᵉ sᵉ Qᵉ)
      ( qᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {xᵉ : Xᵉ} (Pᵉ : subtypeᵉ l2ᵉ Xᵉ) (Qᵉ : subtypeᵉ l3ᵉ Xᵉ)
  (pᵉ : is-in-subtypeᵉ Pᵉ xᵉ) (qᵉ : is-in-subtypeᵉ Qᵉ xᵉ)
  where

  has-same-elements-is-singleton-subtypeᵉ :
    is-singleton-subtypeᵉ Pᵉ → is-singleton-subtypeᵉ Qᵉ →
    has-same-elements-subtypeᵉ Pᵉ Qᵉ
  pr1ᵉ (has-same-elements-is-singleton-subtypeᵉ sᵉ tᵉ yᵉ) =
    inclusion-is-singleton-subtypeᵉ Pᵉ Qᵉ pᵉ qᵉ sᵉ yᵉ
  pr2ᵉ (has-same-elements-is-singleton-subtypeᵉ sᵉ tᵉ yᵉ) =
    inclusion-is-singleton-subtypeᵉ Qᵉ Pᵉ qᵉ pᵉ tᵉ yᵉ
```

### The standard singleton subtype `{x}` of a set is the least subtype containing `x`

```agda
module _
  {l1ᵉ : Level} (Xᵉ : Setᵉ l1ᵉ) (xᵉ : type-Setᵉ Xᵉ)
  where

  is-least-subtype-containing-element-Setᵉ :
    is-least-subtype-containing-elementᵉ xᵉ
      ( subtype-standard-singleton-subtypeᵉ Xᵉ xᵉ)
  pr1ᵉ (is-least-subtype-containing-element-Setᵉ Aᵉ) Hᵉ = Hᵉ xᵉ reflᵉ
  pr2ᵉ (is-least-subtype-containing-element-Setᵉ Aᵉ) Hᵉ .xᵉ reflᵉ = Hᵉ
```

### The image of the standard singleton subtype `{x}` under a map `f : X → Y` is the standard singleton subtype `{f(x)}`

**Proof:**ᵉ Ourᵉ goalᵉ isᵉ to showᵉ thatᵉ theᵉ typeᵉ

```text
  Σᵉ Yᵉ (λ yᵉ → ∥ᵉ Σᵉ (Σᵉ Xᵉ (λ uᵉ → xᵉ ＝ᵉ uᵉ)) (λ vᵉ → fᵉ (inclusionᵉ vᵉ) ＝ᵉ yᵉ) ∥ᵉ )
```

Sinceᵉ theᵉ typeᵉ `Σᵉ Xᵉ (λ uᵉ → xᵉ ＝ᵉ u)`ᵉ isᵉ contractible,ᵉ theᵉ aboveᵉ typeᵉ isᵉ
[equivalent](foundation-core.equivalences.mdᵉ) to

```text
  Σᵉ Yᵉ (λ yᵉ → ∥ᵉ fᵉ xᵉ ＝ᵉ yᵉ ∥ᵉ )
```

Noteᵉ thatᵉ theᵉ identityᵉ typeᵉ `fᵉ xᵉ ＝ᵉ y`ᵉ ofᵉ aᵉ [set](foundation-core.sets.mdᵉ) isᵉ aᵉ
proposition,ᵉ soᵉ thisᵉ typeᵉ isᵉ equivalentᵉ to theᵉ typeᵉ `Σᵉ Yᵉ (λ yᵉ → fᵉ xᵉ ＝ᵉ y)`,ᵉ
whichᵉ isᵉ ofᵉ courseᵉ contractible.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Setᵉ l1ᵉ) (Yᵉ : Setᵉ l2ᵉ) (fᵉ : hom-Setᵉ Xᵉ Yᵉ) (xᵉ : type-Setᵉ Xᵉ)
  where

  abstract
    is-singleton-im-singleton-subtypeᵉ :
      is-singleton-subtypeᵉ
        ( im-subtypeᵉ fᵉ (subtype-standard-singleton-subtypeᵉ Xᵉ xᵉ))
    is-singleton-im-singleton-subtypeᵉ =
      is-contr-equivᵉ
        ( Σᵉ (type-Setᵉ Yᵉ) (λ yᵉ → fᵉ xᵉ ＝ᵉ yᵉ))
        ( equiv-totᵉ
            ( λ yᵉ →
              ( inv-equivᵉ (equiv-unit-trunc-Propᵉ (Id-Propᵉ Yᵉ (fᵉ xᵉ) yᵉ))) ∘eᵉ
              ( equiv-trunc-Propᵉ
                ( left-unit-law-Σ-is-contrᵉ (is-torsorial-Idᵉ xᵉ) (xᵉ ,ᵉ reflᵉ)))))
        ( is-torsorial-Idᵉ (fᵉ xᵉ))

  compute-im-singleton-subtypeᵉ :
    has-same-elements-subtypeᵉ
      ( subtype-standard-singleton-subtypeᵉ Yᵉ (fᵉ xᵉ))
      ( im-subtypeᵉ fᵉ (subtype-standard-singleton-subtypeᵉ Xᵉ xᵉ))
  compute-im-singleton-subtypeᵉ =
    has-same-elements-is-singleton-subtypeᵉ
      ( subtype-standard-singleton-subtypeᵉ Yᵉ (fᵉ xᵉ))
      ( im-subtypeᵉ fᵉ (subtype-standard-singleton-subtypeᵉ Xᵉ xᵉ))
      ( reflᵉ)
      ( unit-trunc-Propᵉ ((xᵉ ,ᵉ reflᵉ) ,ᵉ reflᵉ))
      ( is-torsorial-Idᵉ (fᵉ xᵉ))
      ( is-singleton-im-singleton-subtypeᵉ)
```

## See also

-ᵉ [Connectedᵉ components](foundation.connected-components.mdᵉ)
-ᵉ [Singletonᵉ induction](foundation.singleton-induction.mdᵉ)