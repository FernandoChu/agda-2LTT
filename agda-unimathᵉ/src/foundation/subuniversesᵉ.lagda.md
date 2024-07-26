# Subuniverses

```agda
module foundation.subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

**Subuniverses**ᵉ areᵉ [subtypes](foundation-core.subtypes.mdᵉ) ofᵉ theᵉ universe.ᵉ

## Definitions

### Subuniverses

```agda
is-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
is-subuniverseᵉ Pᵉ = is-subtypeᵉ Pᵉ

subuniverseᵉ :
  (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
subuniverseᵉ l1ᵉ l2ᵉ = subtypeᵉ l2ᵉ (UUᵉ l1ᵉ)

is-subtype-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : UUᵉ l1ᵉ) →
  is-propᵉ (is-in-subtypeᵉ Pᵉ Xᵉ)
is-subtype-subuniverseᵉ Pᵉ Xᵉ = is-prop-is-in-subtypeᵉ Pᵉ Xᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  where

  type-subuniverseᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  type-subuniverseᵉ = type-subtypeᵉ Pᵉ

  is-in-subuniverseᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ
  is-in-subuniverseᵉ = is-in-subtypeᵉ Pᵉ

  is-prop-is-in-subuniverseᵉ : (Xᵉ : UUᵉ l1ᵉ) → is-propᵉ (is-in-subuniverseᵉ Xᵉ)
  is-prop-is-in-subuniverseᵉ = is-prop-is-in-subtypeᵉ Pᵉ

  inclusion-subuniverseᵉ : type-subuniverseᵉ → UUᵉ l1ᵉ
  inclusion-subuniverseᵉ = inclusion-subtypeᵉ Pᵉ

  is-in-subuniverse-inclusion-subuniverseᵉ :
    (Xᵉ : type-subuniverseᵉ) → is-in-subuniverseᵉ (inclusion-subuniverseᵉ Xᵉ)
  is-in-subuniverse-inclusion-subuniverseᵉ = pr2ᵉ

  is-emb-inclusion-subuniverseᵉ : is-embᵉ inclusion-subuniverseᵉ
  is-emb-inclusion-subuniverseᵉ = is-emb-inclusion-subtypeᵉ Pᵉ

  emb-inclusion-subuniverseᵉ : type-subuniverseᵉ ↪ᵉ UUᵉ l1ᵉ
  emb-inclusion-subuniverseᵉ = emb-subtypeᵉ Pᵉ
```

### Maps in a subuniverse

```agda
is-in-subuniverse-mapᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ (l1ᵉ ⊔ l2ᵉ) l3ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Aᵉ → Bᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
is-in-subuniverse-mapᵉ Pᵉ {Aᵉ} {Bᵉ} fᵉ = (bᵉ : Bᵉ) → is-in-subuniverseᵉ Pᵉ (fiberᵉ fᵉ bᵉ)
```

### The predicate of essentially being in a subuniverse

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  where

  is-essentially-in-subuniverseᵉ :
    {l3ᵉ : Level} (Xᵉ : UUᵉ l3ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-essentially-in-subuniverseᵉ Xᵉ =
    Σᵉ (type-subuniverseᵉ Pᵉ) (λ Yᵉ → inclusion-subuniverseᵉ Pᵉ Yᵉ ≃ᵉ Xᵉ)

  is-prop-is-essentially-in-subuniverseᵉ :
    {l3ᵉ : Level} (Xᵉ : UUᵉ l3ᵉ) → is-propᵉ (is-essentially-in-subuniverseᵉ Xᵉ)
  is-prop-is-essentially-in-subuniverseᵉ Xᵉ =
    is-prop-is-proof-irrelevantᵉ
      ( λ ((X'ᵉ ,ᵉ pᵉ) ,ᵉ eᵉ) →
        is-torsorial-Eq-subtypeᵉ
          ( is-contr-equiv'ᵉ
            ( Σᵉ (UUᵉ _) (λ Tᵉ → Tᵉ ≃ᵉ X'ᵉ))
            ( equiv-totᵉ (equiv-postcomp-equivᵉ eᵉ))
            ( is-torsorial-equiv'ᵉ X'ᵉ))
          ( is-prop-is-in-subuniverseᵉ Pᵉ)
          ( X'ᵉ)
          ( eᵉ)
          ( pᵉ))

  is-essentially-in-subuniverse-Propᵉ :
    {l3ᵉ : Level} (Xᵉ : UUᵉ l3ᵉ) → Propᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ (is-essentially-in-subuniverse-Propᵉ Xᵉ) =
    is-essentially-in-subuniverseᵉ Xᵉ
  pr2ᵉ (is-essentially-in-subuniverse-Propᵉ Xᵉ) =
    is-prop-is-essentially-in-subuniverseᵉ Xᵉ
```

## Properties

### Subuniverses are closed under equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) {Xᵉ Yᵉ : UUᵉ l1ᵉ}
  where

  is-in-subuniverse-equivᵉ :
    Xᵉ ≃ᵉ Yᵉ → is-in-subuniverseᵉ Pᵉ Xᵉ → is-in-subuniverseᵉ Pᵉ Yᵉ
  is-in-subuniverse-equivᵉ eᵉ = trᵉ (is-in-subuniverseᵉ Pᵉ) (eq-equivᵉ eᵉ)

  is-in-subuniverse-equiv'ᵉ :
    Xᵉ ≃ᵉ Yᵉ → is-in-subuniverseᵉ Pᵉ Yᵉ → is-in-subuniverseᵉ Pᵉ Xᵉ
  is-in-subuniverse-equiv'ᵉ eᵉ = trᵉ (is-in-subuniverseᵉ Pᵉ) (invᵉ (eq-equivᵉ eᵉ))
```

### Characterization of the identity type of subuniverses

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  where

  equiv-subuniverseᵉ : (Xᵉ Yᵉ : type-subuniverseᵉ Pᵉ) → UUᵉ l1ᵉ
  equiv-subuniverseᵉ Xᵉ Yᵉ = (pr1ᵉ Xᵉ) ≃ᵉ (pr1ᵉ Yᵉ)

  equiv-eq-subuniverseᵉ :
    (Xᵉ Yᵉ : type-subuniverseᵉ Pᵉ) → Xᵉ ＝ᵉ Yᵉ → equiv-subuniverseᵉ Xᵉ Yᵉ
  equiv-eq-subuniverseᵉ Xᵉ .Xᵉ reflᵉ = id-equivᵉ

  abstract
    is-torsorial-equiv-subuniverseᵉ :
      (Xᵉ : type-subuniverseᵉ Pᵉ) →
      is-torsorialᵉ (λ Yᵉ → equiv-subuniverseᵉ Xᵉ Yᵉ)
    is-torsorial-equiv-subuniverseᵉ (Xᵉ ,ᵉ pᵉ) =
      is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-equivᵉ Xᵉ)
        ( is-subtype-subuniverseᵉ Pᵉ)
        ( Xᵉ)
        ( id-equivᵉ)
        ( pᵉ)

    is-torsorial-equiv-subuniverse'ᵉ :
      (Xᵉ : type-subuniverseᵉ Pᵉ) →
      is-torsorialᵉ (λ Yᵉ → equiv-subuniverseᵉ Yᵉ Xᵉ)
    is-torsorial-equiv-subuniverse'ᵉ (Xᵉ ,ᵉ pᵉ) =
      is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-equiv'ᵉ Xᵉ)
        ( is-subtype-subuniverseᵉ Pᵉ)
        ( Xᵉ)
        ( id-equivᵉ)
        ( pᵉ)

  abstract
    is-equiv-equiv-eq-subuniverseᵉ :
      (Xᵉ Yᵉ : type-subuniverseᵉ Pᵉ) → is-equivᵉ (equiv-eq-subuniverseᵉ Xᵉ Yᵉ)
    is-equiv-equiv-eq-subuniverseᵉ Xᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-equiv-subuniverseᵉ Xᵉ)
        ( equiv-eq-subuniverseᵉ Xᵉ)

  extensionality-subuniverseᵉ :
    (Xᵉ Yᵉ : type-subuniverseᵉ Pᵉ) → (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-subuniverseᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-subuniverseᵉ Xᵉ Yᵉ) = equiv-eq-subuniverseᵉ Xᵉ Yᵉ
  pr2ᵉ (extensionality-subuniverseᵉ Xᵉ Yᵉ) = is-equiv-equiv-eq-subuniverseᵉ Xᵉ Yᵉ

  eq-equiv-subuniverseᵉ :
    {Xᵉ Yᵉ : type-subuniverseᵉ Pᵉ} → equiv-subuniverseᵉ Xᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
  eq-equiv-subuniverseᵉ {Xᵉ} {Yᵉ} =
    map-inv-is-equivᵉ (is-equiv-equiv-eq-subuniverseᵉ Xᵉ Yᵉ)

  compute-eq-equiv-id-equiv-subuniverseᵉ :
    {Xᵉ : type-subuniverseᵉ Pᵉ} →
    eq-equiv-subuniverseᵉ {Xᵉ} {Xᵉ} (id-equivᵉ {Aᵉ = pr1ᵉ Xᵉ}) ＝ᵉ reflᵉ
  compute-eq-equiv-id-equiv-subuniverseᵉ =
    is-retraction-map-inv-equivᵉ (extensionality-subuniverseᵉ _ _) reflᵉ
```

### Equivalences of families of types in a subuniverse

```agda
fam-subuniverseᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Xᵉ : UUᵉ l3ᵉ) →
  UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
fam-subuniverseᵉ Pᵉ Xᵉ = Xᵉ → type-subuniverseᵉ Pᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  where

  equiv-fam-subuniverseᵉ :
    (Yᵉ Zᵉ : fam-subuniverseᵉ Pᵉ Xᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  equiv-fam-subuniverseᵉ Yᵉ Zᵉ = (xᵉ : Xᵉ) → equiv-subuniverseᵉ Pᵉ (Yᵉ xᵉ) (Zᵉ xᵉ)

  id-equiv-fam-subuniverseᵉ :
    (Yᵉ : fam-subuniverseᵉ Pᵉ Xᵉ) → equiv-fam-subuniverseᵉ Yᵉ Yᵉ
  id-equiv-fam-subuniverseᵉ Yᵉ xᵉ = id-equivᵉ

  is-torsorial-equiv-fam-subuniverseᵉ :
    (Yᵉ : fam-subuniverseᵉ Pᵉ Xᵉ) →
    is-torsorialᵉ (equiv-fam-subuniverseᵉ Yᵉ)
  is-torsorial-equiv-fam-subuniverseᵉ Yᵉ =
    is-torsorial-Eq-Πᵉ (λ xᵉ → is-torsorial-equiv-subuniverseᵉ Pᵉ (Yᵉ xᵉ))

  equiv-eq-fam-subuniverseᵉ :
    (Yᵉ Zᵉ : fam-subuniverseᵉ Pᵉ Xᵉ) → Yᵉ ＝ᵉ Zᵉ → equiv-fam-subuniverseᵉ Yᵉ Zᵉ
  equiv-eq-fam-subuniverseᵉ Yᵉ .Yᵉ reflᵉ = id-equiv-fam-subuniverseᵉ Yᵉ

  is-equiv-equiv-eq-fam-subuniverseᵉ :
    (Yᵉ Zᵉ : fam-subuniverseᵉ Pᵉ Xᵉ) → is-equivᵉ (equiv-eq-fam-subuniverseᵉ Yᵉ Zᵉ)
  is-equiv-equiv-eq-fam-subuniverseᵉ Yᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-fam-subuniverseᵉ Yᵉ)
      ( equiv-eq-fam-subuniverseᵉ Yᵉ)

  extensionality-fam-subuniverseᵉ :
    (Yᵉ Zᵉ : fam-subuniverseᵉ Pᵉ Xᵉ) → (Yᵉ ＝ᵉ Zᵉ) ≃ᵉ equiv-fam-subuniverseᵉ Yᵉ Zᵉ
  pr1ᵉ (extensionality-fam-subuniverseᵉ Yᵉ Zᵉ) = equiv-eq-fam-subuniverseᵉ Yᵉ Zᵉ
  pr2ᵉ (extensionality-fam-subuniverseᵉ Yᵉ Zᵉ) =
    is-equiv-equiv-eq-fam-subuniverseᵉ Yᵉ Zᵉ

  eq-equiv-fam-subuniverseᵉ :
    (Yᵉ Zᵉ : fam-subuniverseᵉ Pᵉ Xᵉ) → equiv-fam-subuniverseᵉ Yᵉ Zᵉ → (Yᵉ ＝ᵉ Zᵉ)
  eq-equiv-fam-subuniverseᵉ Yᵉ Zᵉ =
    map-inv-is-equivᵉ (is-equiv-equiv-eq-fam-subuniverseᵉ Yᵉ Zᵉ)
```

## See also

-ᵉ [Σ-closedᵉ subuniverses](foundation.sigma-closed-subuniverses.mdᵉ)