# Locales

```agda
module order-theory.localesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.framesᵉ
open import order-theory.greatest-lower-bounds-posetsᵉ
open import order-theory.least-upper-bounds-posetsᵉ
open import order-theory.meet-semilatticesᵉ
open import order-theory.meet-suplatticesᵉ
open import order-theory.posetsᵉ
open import order-theory.suplatticesᵉ
```

</details>

## Idea

Aᵉ **locale**ᵉ isᵉ anᵉ objectᵉ in theᵉ oppositeᵉ ofᵉ theᵉ categoryᵉ ofᵉ
[frames](order-theory.frames.md).ᵉ Inᵉ otherᵉ words,ᵉ aᵉ localeᵉ isᵉ justᵉ aᵉ frame.ᵉ

## Definition

```agda
Localeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Localeᵉ l1ᵉ l2ᵉ = Frameᵉ l1ᵉ l2ᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Lᵉ : Localeᵉ l1ᵉ l2ᵉ)
  where

  meet-suplattice-Localeᵉ : Meet-Suplatticeᵉ l1ᵉ l2ᵉ
  meet-suplattice-Localeᵉ = meet-suplattice-Frameᵉ Lᵉ

  meet-semilattice-Localeᵉ : Meet-Semilatticeᵉ l1ᵉ
  meet-semilattice-Localeᵉ = meet-semilattice-Frameᵉ Lᵉ

  suplattice-Localeᵉ : Suplatticeᵉ l1ᵉ l1ᵉ l2ᵉ
  suplattice-Localeᵉ = suplattice-Frameᵉ Lᵉ

  poset-Localeᵉ : Posetᵉ l1ᵉ l1ᵉ
  poset-Localeᵉ = poset-Frameᵉ Lᵉ

  set-Localeᵉ : Setᵉ l1ᵉ
  set-Localeᵉ = set-Frameᵉ Lᵉ

  type-Localeᵉ : UUᵉ l1ᵉ
  type-Localeᵉ = type-Frameᵉ Lᵉ

  is-set-type-Localeᵉ : is-setᵉ type-Localeᵉ
  is-set-type-Localeᵉ = is-set-type-Frameᵉ Lᵉ

  leq-Locale-Propᵉ : (xᵉ yᵉ : type-Localeᵉ) → Propᵉ l1ᵉ
  leq-Locale-Propᵉ = leq-Frame-Propᵉ Lᵉ

  leq-Localeᵉ : (xᵉ yᵉ : type-Localeᵉ) → UUᵉ l1ᵉ
  leq-Localeᵉ = leq-Frameᵉ Lᵉ

  is-prop-leq-Localeᵉ : (xᵉ yᵉ : type-Localeᵉ) → is-propᵉ (leq-Localeᵉ xᵉ yᵉ)
  is-prop-leq-Localeᵉ = is-prop-leq-Frameᵉ Lᵉ

  refl-leq-Localeᵉ : is-reflexiveᵉ leq-Localeᵉ
  refl-leq-Localeᵉ = refl-leq-Frameᵉ Lᵉ

  antisymmetric-leq-Localeᵉ : is-antisymmetricᵉ leq-Localeᵉ
  antisymmetric-leq-Localeᵉ = antisymmetric-leq-Frameᵉ Lᵉ

  transitive-leq-Localeᵉ : is-transitiveᵉ leq-Localeᵉ
  transitive-leq-Localeᵉ = transitive-leq-Frameᵉ Lᵉ

  meet-Localeᵉ : type-Localeᵉ → type-Localeᵉ → type-Localeᵉ
  meet-Localeᵉ = meet-Frameᵉ Lᵉ

  is-greatest-binary-lower-bound-meet-Localeᵉ :
    (xᵉ yᵉ : type-Localeᵉ) →
    is-greatest-binary-lower-bound-Posetᵉ poset-Localeᵉ xᵉ yᵉ (meet-Localeᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-Localeᵉ =
    is-greatest-binary-lower-bound-meet-Frameᵉ Lᵉ

  associative-meet-Localeᵉ :
    (xᵉ yᵉ zᵉ : type-Localeᵉ) →
    meet-Localeᵉ (meet-Localeᵉ xᵉ yᵉ) zᵉ ＝ᵉ meet-Localeᵉ xᵉ (meet-Localeᵉ yᵉ zᵉ)
  associative-meet-Localeᵉ = associative-meet-Frameᵉ Lᵉ

  commutative-meet-Localeᵉ :
    (xᵉ yᵉ : type-Localeᵉ) → meet-Localeᵉ xᵉ yᵉ ＝ᵉ meet-Localeᵉ yᵉ xᵉ
  commutative-meet-Localeᵉ = commutative-meet-Frameᵉ Lᵉ

  idempotent-meet-Localeᵉ :
    (xᵉ : type-Localeᵉ) → meet-Localeᵉ xᵉ xᵉ ＝ᵉ xᵉ
  idempotent-meet-Localeᵉ = idempotent-meet-Frameᵉ Lᵉ

  is-suplattice-Localeᵉ :
    is-suplattice-Posetᵉ l2ᵉ poset-Localeᵉ
  is-suplattice-Localeᵉ = is-suplattice-Frameᵉ Lᵉ

  sup-Localeᵉ : {Iᵉ : UUᵉ l2ᵉ} → (Iᵉ → type-Localeᵉ) → type-Localeᵉ
  sup-Localeᵉ = sup-Frameᵉ Lᵉ

  is-least-upper-bound-sup-Localeᵉ :
    {Iᵉ : UUᵉ l2ᵉ} (xᵉ : Iᵉ → type-Localeᵉ) →
    is-least-upper-bound-family-of-elements-Posetᵉ poset-Localeᵉ xᵉ (sup-Localeᵉ xᵉ)
  is-least-upper-bound-sup-Localeᵉ = is-least-upper-bound-sup-Frameᵉ Lᵉ

  distributive-meet-sup-Localeᵉ :
    distributive-law-Meet-Suplatticeᵉ meet-suplattice-Localeᵉ
  distributive-meet-sup-Localeᵉ = distributive-meet-sup-Frameᵉ Lᵉ
```