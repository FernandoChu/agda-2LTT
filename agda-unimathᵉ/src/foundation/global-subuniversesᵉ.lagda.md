# Global subuniverses

```agda
module foundation.global-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

**Globalᵉ subuniverses**ᵉ areᵉ [subtypes](foundation-core.subtypes.mdᵉ) ofᵉ theᵉ largeᵉ
universeᵉ thatᵉ areᵉ definedᵉ atᵉ everyᵉ level,ᵉ andᵉ areᵉ closedᵉ underᵉ
[equivalencesᵉ ofᵉ types](foundation-core.equivalences.md).ᵉ Thisᵉ doesᵉ notᵉ followᵉ
fromᵉ [univalence](foundation.univalence.md),ᵉ asᵉ equivalenceᵉ inductionᵉ onlyᵉ holdsᵉ
forᵉ homogeneousᵉ equivalences,ᵉ i.e.ᵉ equivalencesᵉ in aᵉ singleᵉ universe.ᵉ

## Definitions

### The predicate on families of subuniverses of being closed under equivalences

```agda
module _
  (αᵉ : Level → Level) (Pᵉ : (lᵉ : Level) → subuniverseᵉ lᵉ (αᵉ lᵉ))
  (l1ᵉ l2ᵉ : Level)
  where

  is-closed-under-equiv-subuniversesᵉ : UUᵉ (αᵉ l1ᵉ ⊔ αᵉ l2ᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ)
  is-closed-under-equiv-subuniversesᵉ =
    (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : UUᵉ l2ᵉ) → Xᵉ ≃ᵉ Yᵉ → type-Propᵉ (Pᵉ l1ᵉ Xᵉ) → type-Propᵉ (Pᵉ l2ᵉ Yᵉ)

  is-prop-is-closed-under-equiv-subuniversesᵉ :
    is-propᵉ is-closed-under-equiv-subuniversesᵉ
  is-prop-is-closed-under-equiv-subuniversesᵉ =
    is-prop-iterated-Πᵉ 4 (λ Xᵉ Yᵉ eᵉ xᵉ → is-prop-type-Propᵉ (Pᵉ l2ᵉ Yᵉ))

  is-closed-under-equiv-subuniverses-Propᵉ :
    Propᵉ (αᵉ l1ᵉ ⊔ αᵉ l2ᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ)
  pr1ᵉ is-closed-under-equiv-subuniverses-Propᵉ =
    is-closed-under-equiv-subuniversesᵉ
  pr2ᵉ is-closed-under-equiv-subuniverses-Propᵉ =
    is-prop-is-closed-under-equiv-subuniversesᵉ
```

### The global type of global subuniverses

```agda
record global-subuniverseᵉ (αᵉ : Level → Level) : UUωᵉ where
  field
    subuniverse-global-subuniverseᵉ :
      (lᵉ : Level) → subuniverseᵉ lᵉ (αᵉ lᵉ)

    is-closed-under-equiv-global-subuniverseᵉ :
      (l1ᵉ l2ᵉ : Level) →
      is-closed-under-equiv-subuniversesᵉ αᵉ subuniverse-global-subuniverseᵉ l1ᵉ l2ᵉ

open global-subuniverseᵉ public

module _
  {αᵉ : Level → Level} (Pᵉ : global-subuniverseᵉ αᵉ)
  where

  is-in-global-subuniverseᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ (αᵉ lᵉ)
  is-in-global-subuniverseᵉ {lᵉ} Xᵉ =
    is-in-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ lᵉ) Xᵉ

  type-global-subuniverseᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ ⊔ lsuc lᵉ)
  type-global-subuniverseᵉ lᵉ =
    type-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ lᵉ)

  inclusion-global-subuniverseᵉ :
    {lᵉ : Level} → type-global-subuniverseᵉ lᵉ → UUᵉ lᵉ
  inclusion-global-subuniverseᵉ {lᵉ} =
    inclusion-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ lᵉ)
```

### Maps in a subuniverse

Weᵉ sayᵉ aᵉ mapᵉ isᵉ _inᵉ_ aᵉ globalᵉ subuniverseᵉ ifᵉ eachᵉ ofᵉ itsᵉ
[fibers](foundation-core.fibers-of-maps.mdᵉ) is.ᵉ

```agda
module _
  {αᵉ : Level → Level} (Pᵉ : global-subuniverseᵉ αᵉ)
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-in-map-global-subuniverseᵉ : (Aᵉ → Bᵉ) → UUᵉ (αᵉ (l1ᵉ ⊔ l2ᵉ) ⊔ l2ᵉ)
  is-in-map-global-subuniverseᵉ fᵉ =
    (yᵉ : Bᵉ) →
    is-in-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ (l1ᵉ ⊔ l2ᵉ)) (fiberᵉ fᵉ yᵉ)
```

### The predicate of essentially being in a subuniverse

Weᵉ sayᵉ aᵉ typeᵉ isᵉ _essentiallyᵉ inᵉ_ aᵉ globalᵉ universeᵉ atᵉ universeᵉ levelᵉ `l`ᵉ ifᵉ itᵉ
isᵉ essentiallyᵉ in theᵉ subuniverseᵉ atᵉ levelᵉ `l`.ᵉ

```agda
module _
  {αᵉ : Level → Level} (Pᵉ : global-subuniverseᵉ αᵉ)
  {l1ᵉ : Level} (l2ᵉ : Level) (Xᵉ : UUᵉ l1ᵉ)
  where

  is-essentially-in-global-subuniverseᵉ : UUᵉ (αᵉ l2ᵉ ⊔ l1ᵉ ⊔ lsuc l2ᵉ)
  is-essentially-in-global-subuniverseᵉ =
    is-essentially-in-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ l2ᵉ) Xᵉ

  is-prop-is-essentially-in-global-subuniverseᵉ :
    is-propᵉ is-essentially-in-global-subuniverseᵉ
  is-prop-is-essentially-in-global-subuniverseᵉ =
    is-prop-is-essentially-in-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Pᵉ l2ᵉ) Xᵉ

  is-essentially-in-global-subuniverse-Propᵉ : Propᵉ (αᵉ l2ᵉ ⊔ l1ᵉ ⊔ lsuc l2ᵉ)
  is-essentially-in-global-subuniverse-Propᵉ =
    is-essentially-in-subuniverse-Propᵉ (subuniverse-global-subuniverseᵉ Pᵉ l2ᵉ) Xᵉ
```

## Properties

### Global subuniverses are closed under homogenous equivalences

Thisᵉ isᵉ trueᵉ forᵉ anyᵉ familyᵉ ofᵉ subuniversesᵉ indexedᵉ byᵉ universeᵉ levels.ᵉ

```agda
module _
  {αᵉ : Level → Level} (Pᵉ : global-subuniverseᵉ αᵉ)
  {lᵉ : Level} {Xᵉ Yᵉ : UUᵉ lᵉ}
  where

  is-in-global-subuniverse-homogenous-equivᵉ :
    Xᵉ ≃ᵉ Yᵉ → is-in-global-subuniverseᵉ Pᵉ Xᵉ → is-in-global-subuniverseᵉ Pᵉ Yᵉ
  is-in-global-subuniverse-homogenous-equivᵉ =
    is-in-subuniverse-equivᵉ (subuniverse-global-subuniverseᵉ Pᵉ lᵉ)

  is-in-global-subuniverse-homogenous-equiv'ᵉ :
    Xᵉ ≃ᵉ Yᵉ → is-in-global-subuniverseᵉ Pᵉ Yᵉ → is-in-global-subuniverseᵉ Pᵉ Xᵉ
  is-in-global-subuniverse-homogenous-equiv'ᵉ =
    is-in-subuniverse-equiv'ᵉ (subuniverse-global-subuniverseᵉ Pᵉ lᵉ)
```

### Characterization of the identity type of global subuniverses at a universe level

```agda
module _
  {αᵉ : Level → Level} {lᵉ : Level} (Pᵉ : global-subuniverseᵉ αᵉ)
  where

  equiv-global-subuniverse-Levelᵉ : (Xᵉ Yᵉ : type-global-subuniverseᵉ Pᵉ lᵉ) → UUᵉ lᵉ
  equiv-global-subuniverse-Levelᵉ =
    equiv-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ lᵉ)

  equiv-eq-global-subuniverse-Levelᵉ :
    (Xᵉ Yᵉ : type-global-subuniverseᵉ Pᵉ lᵉ) →
    Xᵉ ＝ᵉ Yᵉ → equiv-global-subuniverse-Levelᵉ Xᵉ Yᵉ
  equiv-eq-global-subuniverse-Levelᵉ =
    equiv-eq-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ lᵉ)

  abstract
    is-equiv-equiv-eq-global-subuniverse-Levelᵉ :
      (Xᵉ Yᵉ : type-global-subuniverseᵉ Pᵉ lᵉ) →
      is-equivᵉ (equiv-eq-global-subuniverse-Levelᵉ Xᵉ Yᵉ)
    is-equiv-equiv-eq-global-subuniverse-Levelᵉ =
      is-equiv-equiv-eq-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ lᵉ)

  extensionality-global-subuniverse-Levelᵉ :
    (Xᵉ Yᵉ : type-global-subuniverseᵉ Pᵉ lᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-global-subuniverse-Levelᵉ Xᵉ Yᵉ
  extensionality-global-subuniverse-Levelᵉ =
    extensionality-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ lᵉ)

  eq-equiv-global-subuniverse-Levelᵉ :
    {Xᵉ Yᵉ : type-global-subuniverseᵉ Pᵉ lᵉ} →
    equiv-global-subuniverse-Levelᵉ Xᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
  eq-equiv-global-subuniverse-Levelᵉ =
    eq-equiv-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ lᵉ)

  compute-eq-equiv-id-equiv-global-subuniverse-Levelᵉ :
    {Xᵉ : type-global-subuniverseᵉ Pᵉ lᵉ} →
    eq-equiv-global-subuniverse-Levelᵉ {Xᵉ} {Xᵉ} (id-equivᵉ {Aᵉ = pr1ᵉ Xᵉ}) ＝ᵉ reflᵉ
  compute-eq-equiv-id-equiv-global-subuniverse-Levelᵉ =
    compute-eq-equiv-id-equiv-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ lᵉ)
```

### Equivalences of families of types in a global subuniverse

```agda
fam-global-subuniverseᵉ :
  {αᵉ : Level → Level} (Pᵉ : global-subuniverseᵉ αᵉ)
  {l1ᵉ : Level} (l2ᵉ : Level) (Xᵉ : UUᵉ l1ᵉ) → UUᵉ (αᵉ l2ᵉ ⊔ l1ᵉ ⊔ lsuc l2ᵉ)
fam-global-subuniverseᵉ Pᵉ l2ᵉ Xᵉ = Xᵉ → type-global-subuniverseᵉ Pᵉ l2ᵉ

module _
  {αᵉ : Level → Level} (Pᵉ : global-subuniverseᵉ αᵉ)
  {l1ᵉ : Level} (l2ᵉ : Level) {Xᵉ : UUᵉ l1ᵉ}
  (Yᵉ Zᵉ : fam-global-subuniverseᵉ Pᵉ l2ᵉ Xᵉ)
  where

  equiv-fam-global-subuniverseᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-fam-global-subuniverseᵉ =
    equiv-fam-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ l2ᵉ) Yᵉ Zᵉ

  equiv-eq-fam-global-subuniverseᵉ :
    Yᵉ ＝ᵉ Zᵉ → equiv-fam-global-subuniverseᵉ
  equiv-eq-fam-global-subuniverseᵉ =
    equiv-eq-fam-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ l2ᵉ) Yᵉ Zᵉ

  is-equiv-equiv-eq-fam-global-subuniverseᵉ :
    is-equivᵉ equiv-eq-fam-global-subuniverseᵉ
  is-equiv-equiv-eq-fam-global-subuniverseᵉ =
    is-equiv-equiv-eq-fam-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ l2ᵉ) Yᵉ Zᵉ

  extensionality-fam-global-subuniverseᵉ :
    (Yᵉ ＝ᵉ Zᵉ) ≃ᵉ equiv-fam-global-subuniverseᵉ
  extensionality-fam-global-subuniverseᵉ =
    extensionality-fam-subuniverseᵉ (subuniverse-global-subuniverseᵉ Pᵉ l2ᵉ) Yᵉ Zᵉ

  eq-equiv-fam-global-subuniverseᵉ : equiv-fam-global-subuniverseᵉ → Yᵉ ＝ᵉ Zᵉ
  eq-equiv-fam-global-subuniverseᵉ =
    map-inv-is-equivᵉ is-equiv-equiv-eq-fam-global-subuniverseᵉ
```

## See also

-ᵉ [Largeᵉ categories](category-theory.large-categories.mdᵉ)