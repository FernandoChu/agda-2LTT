# Global function classes

```agda
module orthogonal-factorization-systems.global-function-classesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.propositionsᵉ
open import foundation.pullbacksᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.function-classesᵉ
```

</details>

## Idea

Aᵉ **globalᵉ functionᵉ class**ᵉ isᵉ aᵉ globalᵉ [subtype](foundation.subtypes.mdᵉ) ofᵉ
functionᵉ typesᵉ thatᵉ isᵉ closedᵉ underᵉ compositionᵉ with
[equivalences](foundation-core.equivalences.md).ᵉ

Noteᵉ thatᵉ compositionᵉ with homogenousᵉ equivalencesᵉ followsᵉ fromᵉ
[univalence](foundation.univalence.md),ᵉ soᵉ thisᵉ conditionᵉ shouldᵉ holdᵉ forᵉ theᵉ
correctᵉ universeᵉ polymorphicᵉ definition.ᵉ

## Definitions

### The predicate on families of function classes of being closed under composition with equivalences

```agda
module _
  {βᵉ : Level → Level → Level}
  (Pᵉ : {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → subtypeᵉ (βᵉ l1ᵉ l2ᵉ) (Aᵉ → Bᵉ))
  where

  is-closed-under-equiv-precomp-function-classesᵉ :
    (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l3ᵉ l2ᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
  is-closed-under-equiv-precomp-function-classesᵉ l1ᵉ l2ᵉ l3ᵉ =
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ) → is-in-subtypeᵉ Pᵉ fᵉ →
    (eᵉ : Cᵉ ≃ᵉ Aᵉ) → is-in-subtypeᵉ Pᵉ (fᵉ ∘ᵉ map-equivᵉ eᵉ)

  is-closed-under-equiv-postcomp-function-classesᵉ :
    (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l1ᵉ l3ᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
  is-closed-under-equiv-postcomp-function-classesᵉ l1ᵉ l2ᵉ l3ᵉ =
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ) → is-in-subtypeᵉ Pᵉ fᵉ →
    (eᵉ : Bᵉ ≃ᵉ Cᵉ) → is-in-subtypeᵉ Pᵉ (map-equivᵉ eᵉ ∘ᵉ fᵉ)
```

### The large type of global function classes

```agda
record global-function-classᵉ (βᵉ : Level → Level → Level) : UUωᵉ where
  field
    function-class-global-function-classᵉ :
      {l1ᵉ l2ᵉ : Level} → function-classᵉ l1ᵉ l2ᵉ (βᵉ l1ᵉ l2ᵉ)

    is-closed-under-equiv-precomp-global-function-classᵉ :
      {l1ᵉ l2ᵉ l3ᵉ : Level} →
      is-closed-under-equiv-precomp-function-classesᵉ
        ( function-class-global-function-classᵉ)
        l1ᵉ l2ᵉ l3ᵉ

    is-closed-under-equiv-postcomp-global-function-classᵉ :
      {l1ᵉ l2ᵉ l3ᵉ : Level} →
      is-closed-under-equiv-postcomp-function-classesᵉ
        ( function-class-global-function-classᵉ)
        l1ᵉ l2ᵉ l3ᵉ

open global-function-classᵉ public

type-global-function-classᵉ :
  {βᵉ : Level → Level → Level} (Pᵉ : global-function-classᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (βᵉ l1ᵉ l2ᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
type-global-function-classᵉ Pᵉ =
  type-function-classᵉ (function-class-global-function-classᵉ Pᵉ)

module _
  {βᵉ : Level → Level → Level} (Pᵉ : global-function-classᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-in-global-function-classᵉ : (Aᵉ → Bᵉ) → UUᵉ (βᵉ l1ᵉ l2ᵉ)
  is-in-global-function-classᵉ =
    is-in-function-classᵉ (function-class-global-function-classᵉ Pᵉ)

  is-prop-is-in-global-function-classᵉ :
    (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (is-in-global-function-classᵉ fᵉ)
  is-prop-is-in-global-function-classᵉ =
    is-prop-is-in-function-classᵉ (function-class-global-function-classᵉ Pᵉ)

  inclusion-global-function-classᵉ : type-global-function-classᵉ Pᵉ Aᵉ Bᵉ → Aᵉ → Bᵉ
  inclusion-global-function-classᵉ =
    inclusion-function-classᵉ (function-class-global-function-classᵉ Pᵉ)

  is-emb-inclusion-global-function-classᵉ :
    is-embᵉ inclusion-global-function-classᵉ
  is-emb-inclusion-global-function-classᵉ =
    is-emb-inclusion-function-classᵉ (function-class-global-function-classᵉ Pᵉ)

  emb-global-function-classᵉ : type-global-function-classᵉ Pᵉ Aᵉ Bᵉ ↪ᵉ (Aᵉ → Bᵉ)
  emb-global-function-classᵉ =
    emb-function-classᵉ (function-class-global-function-classᵉ Pᵉ)
```

### Global function classes containing identities

```agda
module _
  {βᵉ : Level → Level → Level} (Pᵉ : global-function-classᵉ βᵉ)
  where

  has-identity-maps-global-function-class-Levelᵉ :
    (lᵉ : Level) → UUᵉ (βᵉ lᵉ lᵉ ⊔ lsuc lᵉ)
  has-identity-maps-global-function-class-Levelᵉ lᵉ =
    (Aᵉ : UUᵉ lᵉ) → is-in-global-function-classᵉ Pᵉ (idᵉ {Aᵉ = Aᵉ})

  has-identity-maps-global-function-classᵉ : UUωᵉ
  has-identity-maps-global-function-classᵉ =
    {lᵉ : Level} → has-identity-maps-global-function-class-Levelᵉ lᵉ
```

### Global function classes containing equivalences

```agda
module _
  {βᵉ : Level → Level → Level} (Pᵉ : global-function-classᵉ βᵉ)
  where

  has-equivalences-global-function-class-Levelᵉ :
    (l1ᵉ l2ᵉ : Level) → UUᵉ (βᵉ l1ᵉ l2ᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ)
  has-equivalences-global-function-class-Levelᵉ l1ᵉ l2ᵉ =
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-equivᵉ fᵉ → is-in-global-function-classᵉ Pᵉ fᵉ

  has-equivalences-global-function-classᵉ : UUωᵉ
  has-equivalences-global-function-classᵉ =
    {l1ᵉ l2ᵉ : Level} → has-equivalences-global-function-class-Levelᵉ l1ᵉ l2ᵉ
```

**Note:**ᵉ Theᵉ previousᵉ twoᵉ conditionsᵉ areᵉ equivalentᵉ byᵉ theᵉ closureᵉ propertyᵉ ofᵉ
globalᵉ functionᵉ classes.ᵉ

### Composition closed function classes

Weᵉ sayᵉ aᵉ functionᵉ classᵉ isᵉ **compositionᵉ closed**ᵉ ifᵉ itᵉ isᵉ closedᵉ underᵉ takingᵉ
composites.ᵉ

```agda
module _
  {βᵉ : Level → Level → Level} (Pᵉ : global-function-classᵉ βᵉ)
  where

  is-closed-under-composition-global-function-class-Levelᵉ :
    (l1ᵉ l2ᵉ l3ᵉ : Level) →
    UUᵉ (βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l1ᵉ l3ᵉ ⊔ βᵉ l2ᵉ l3ᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
  is-closed-under-composition-global-function-class-Levelᵉ l1ᵉ l2ᵉ l3ᵉ =
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {gᵉ : Bᵉ → Cᵉ} {fᵉ : Aᵉ → Bᵉ} →
    is-in-global-function-classᵉ Pᵉ gᵉ →
    is-in-global-function-classᵉ Pᵉ fᵉ →
    is-in-global-function-classᵉ Pᵉ (gᵉ ∘ᵉ fᵉ)

  is-closed-under-composition-global-function-classᵉ : UUωᵉ
  is-closed-under-composition-global-function-classᵉ =
    {l1ᵉ l2ᵉ l3ᵉ : Level} →
    is-closed-under-composition-global-function-class-Levelᵉ l1ᵉ l2ᵉ l3ᵉ
```

## Pullback-stable global function classes

Aᵉ globalᵉ functionᵉ classᵉ isᵉ saidᵉ to beᵉ **pullback-stable**ᵉ ifᵉ givenᵉ aᵉ functionᵉ in
it,ᵉ itsᵉ pullbackᵉ alongᵉ anyᵉ mapᵉ isᵉ alsoᵉ in theᵉ globalᵉ functionᵉ class.ᵉ

```agda
module _
  {βᵉ : Level → Level → Level} (Pᵉ : global-function-classᵉ βᵉ)
  where

  is-pullback-stable-global-function-class-Levelᵉ :
    (l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level) →
    UUᵉ (βᵉ l1ᵉ l3ᵉ ⊔ βᵉ l4ᵉ l2ᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ)
  is-pullback-stable-global-function-class-Levelᵉ l1ᵉ l2ᵉ l3ᵉ l4ᵉ =
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} (fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ)
    (cᵉ : coneᵉ fᵉ gᵉ Xᵉ) (pᵉ : is-pullbackᵉ fᵉ gᵉ cᵉ) →
    is-in-global-function-classᵉ Pᵉ fᵉ →
    is-in-global-function-classᵉ Pᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ)

  is-pullback-stable-global-function-classᵉ : UUωᵉ
  is-pullback-stable-global-function-classᵉ =
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} →
    is-pullback-stable-global-function-class-Levelᵉ l1ᵉ l2ᵉ l3ᵉ l4ᵉ
```

## Properties

### Having identities is equivalent to having equivalences

Thisᵉ followsᵉ fromᵉ eitherᵉ ofᵉ theᵉ closureᵉ propertiesᵉ ofᵉ globalᵉ functionᵉ classes.ᵉ

```agda
module _
  {βᵉ : Level → Level → Level} (Pᵉ : global-function-classᵉ βᵉ)
  where

  has-equivalences-has-identity-maps-global-function-classᵉ :
    has-identity-maps-global-function-classᵉ Pᵉ →
    has-equivalences-global-function-classᵉ Pᵉ
  has-equivalences-has-identity-maps-global-function-classᵉ
    has-id-Pᵉ {Bᵉ = Bᵉ} fᵉ f'ᵉ =
    is-closed-under-equiv-precomp-global-function-classᵉ
      Pᵉ idᵉ (has-id-Pᵉ Bᵉ) (fᵉ ,ᵉ f'ᵉ)

  has-equivalences-has-identity-maps-global-function-class'ᵉ :
    has-identity-maps-global-function-classᵉ Pᵉ →
    has-equivalences-global-function-classᵉ Pᵉ
  has-equivalences-has-identity-maps-global-function-class'ᵉ
    has-id-Pᵉ {Aᵉ = Aᵉ} fᵉ f'ᵉ =
    is-closed-under-equiv-postcomp-global-function-classᵉ
      Pᵉ idᵉ (has-id-Pᵉ Aᵉ) (fᵉ ,ᵉ f'ᵉ)

  has-identity-maps-has-equivalences-global-function-classᵉ :
    has-equivalences-global-function-classᵉ Pᵉ →
    has-identity-maps-global-function-classᵉ Pᵉ
  has-identity-maps-has-equivalences-global-function-classᵉ has-equiv-Pᵉ Aᵉ =
    has-equiv-Pᵉ idᵉ is-equiv-idᵉ
```