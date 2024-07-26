# The large locale of propositions

```agda
module foundation.large-locale-of-propositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunctionᵉ
open import foundation.existential-quantificationᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-cartesian-product-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.propositionsᵉ

open import order-theory.large-framesᵉ
open import order-theory.large-localesᵉ
open import order-theory.large-meet-semilatticesᵉ
open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
open import order-theory.large-suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
open import order-theory.top-elements-large-posetsᵉ
```

</details>

## Idea

Theᵉ [largeᵉ locale](order-theory.large-locales.mdᵉ) ofᵉ
[propositions](foundation-core.propositions.mdᵉ) consistsᵉ ofᵉ allᵉ theᵉ propositionsᵉ
ofᵉ anyᵉ [universeᵉ level](foundation.universe-levels.mdᵉ) andᵉ isᵉ orderedᵉ byᵉ theᵉ
implicationsᵉ betweenᵉ them.ᵉ [Conjunction](foundation.conjunction.mdᵉ) givesᵉ thisᵉ
[largeᵉ poset](order-theory.large-posets.mdᵉ) theᵉ structureᵉ ofᵉ aᵉ
[largeᵉ meet-semilattice](order-theory.large-meet-semilattices.md),ᵉ andᵉ
[existentialᵉ quantification](foundation.existential-quantification.mdᵉ) givesᵉ itᵉ
theᵉ structureᵉ ofᵉ aᵉ [largeᵉ suplattice](order-theory.large-suplattices.md).ᵉ

**Note.**ᵉ Theᵉ collectionᵉ ofᵉ allᵉ propositionsᵉ isᵉ largeᵉ becauseᵉ weᵉ do notᵉ assumeᵉ
[propositionalᵉ resizing](foundation.propositional-resizing.md).ᵉ

## Definitions

### The large preorder of propositions

```agda
Prop-Large-Preorderᵉ : Large-Preorderᵉ lsuc (_⊔ᵉ_)
type-Large-Preorderᵉ Prop-Large-Preorderᵉ = Propᵉ
leq-prop-Large-Preorderᵉ Prop-Large-Preorderᵉ = hom-Propᵉ
refl-leq-Large-Preorderᵉ Prop-Large-Preorderᵉ Pᵉ = idᵉ
transitive-leq-Large-Preorderᵉ Prop-Large-Preorderᵉ Pᵉ Qᵉ Rᵉ gᵉ fᵉ = gᵉ ∘ᵉ fᵉ
```

### The large poset of propositions

```agda
Prop-Large-Posetᵉ : Large-Posetᵉ lsuc (_⊔ᵉ_)
large-preorder-Large-Posetᵉ Prop-Large-Posetᵉ = Prop-Large-Preorderᵉ
antisymmetric-leq-Large-Posetᵉ Prop-Large-Posetᵉ Pᵉ Qᵉ = eq-iffᵉ
```

### Meets in the large poset of propositions

```agda
has-meets-Prop-Large-Localeᵉ :
  has-meets-Large-Posetᵉ Prop-Large-Posetᵉ
meet-has-meets-Large-Posetᵉ has-meets-Prop-Large-Localeᵉ = conjunction-Propᵉ
is-greatest-binary-lower-bound-meet-has-meets-Large-Posetᵉ
  has-meets-Prop-Large-Localeᵉ Pᵉ Qᵉ Rᵉ =
  is-greatest-binary-lower-bound-conjunction-Propᵉ Pᵉ Qᵉ Rᵉ
```

### The largest element in the large poset of propositions

```agda
has-top-element-Prop-Large-Localeᵉ :
  has-top-element-Large-Posetᵉ Prop-Large-Posetᵉ
top-has-top-element-Large-Posetᵉ
  has-top-element-Prop-Large-Localeᵉ = unit-Propᵉ
is-top-element-top-has-top-element-Large-Posetᵉ
  has-top-element-Prop-Large-Localeᵉ Pᵉ pᵉ =
  starᵉ
```

### The large poset of propositions is a large meet-semilattice

```agda
is-large-meet-semilattice-Prop-Large-Localeᵉ :
  is-large-meet-semilattice-Large-Posetᵉ Prop-Large-Posetᵉ
has-meets-is-large-meet-semilattice-Large-Posetᵉ
  is-large-meet-semilattice-Prop-Large-Localeᵉ =
  has-meets-Prop-Large-Localeᵉ
has-top-element-is-large-meet-semilattice-Large-Posetᵉ
  is-large-meet-semilattice-Prop-Large-Localeᵉ =
  has-top-element-Prop-Large-Localeᵉ
```

### Suprema in the large poset of propositions

```agda
is-large-suplattice-Prop-Large-Localeᵉ :
  is-large-suplattice-Large-Posetᵉ lzero Prop-Large-Posetᵉ
sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
  ( is-large-suplattice-Prop-Large-Localeᵉ {Iᵉ = Iᵉ} Pᵉ) =
  ∃ᵉ Iᵉ Pᵉ
is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
  ( is-large-suplattice-Prop-Large-Localeᵉ {Iᵉ = Iᵉ} Pᵉ) Rᵉ =
  inv-iffᵉ (up-existsᵉ Rᵉ)
```

### The large frame of propositions

```agda
Prop-Large-Frameᵉ : Large-Frameᵉ lsuc (_⊔ᵉ_) lzero
large-poset-Large-Frameᵉ Prop-Large-Frameᵉ =
  Prop-Large-Posetᵉ
is-large-meet-semilattice-Large-Frameᵉ Prop-Large-Frameᵉ =
  is-large-meet-semilattice-Prop-Large-Localeᵉ
is-large-suplattice-Large-Frameᵉ Prop-Large-Frameᵉ =
  is-large-suplattice-Prop-Large-Localeᵉ
distributive-meet-sup-Large-Frameᵉ Prop-Large-Frameᵉ =
  eq-distributive-conjunction-existsᵉ
```

### The large locale of propositions

```agda
Prop-Large-Localeᵉ : Large-Localeᵉ lsuc (_⊔ᵉ_) lzero
Prop-Large-Localeᵉ = Prop-Large-Frameᵉ
```

## See also

-ᵉ [Propositionalᵉ resizing](foundation.propositional-resizing.mdᵉ)