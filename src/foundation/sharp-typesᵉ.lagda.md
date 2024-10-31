# Sharp exo-types

```agda
module foundation.sharp-typesᵉ where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.unit-type

open import elementary-number-theory.natural-numbersᵉ

-- open import foundation-core.precomposition-functionsᵉ
open import foundation.pi-decompositionsᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.pi-decompositions
open import foundation.action-on-identifications-functionsᵉ
open import foundation.action-on-identifications-dependent-functions
open import foundation.homotopies
open import foundation.action-on-identifications-functions
open import foundation.cofibrant-typesᵉ
open import foundation.fibrant-typesᵉ
open import foundation.equivalences
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-types
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.function-typesᵉ
open import foundation.function-types
open import foundation.function-extensionality
open import foundation.function-extensionalityᵉ
open import foundation.unit-typeᵉ
open import foundation.transport-along-identifications
open import foundation.transport-along-identificationsᵉ
open import foundation.homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.identity-types
open import foundation.universe-levelsᵉ
open import foundation.equivalencesᵉ
open import foundation.coercing-inner-typesᵉ
open import foundation.sections
open import foundation.universe-levelsᵉ
open import foundation.universe-levels
open import foundation.exotypesᵉ
```

## Idea

## Definition

### Sharp types

```agda
record is-sharp {i : Level} (B : UUᵉ i) (j : Level) : UUᵉ (lsuc (i ⊔ j)) where
  constructor mk-is-sharp
  field
    is-cofibrant-is-sharp : is-cofibrant B j
    fibrant-replacement-is-sharp : UU i
    map-fibrant-replacement-is-sharp :
      B → fibrant-replacement-is-sharp

  precomp-map-is-sharp :
    ( Y : fibrant-replacement-is-sharp → UU j) →
    ( Π fibrant-replacement-is-sharp Y) →
    witness-Fibrant-Type
      ( fibrant-Π-is-cofibrant is-cofibrant-is-sharp
        ( Y ∘ᶠᶠᵉ map-fibrant-replacement-is-sharp))
  precomp-map-is-sharp Y f =
    witness-exotype-is-fibrant
      ( is-fibrant-Π-is-cofibrant
        ( is-cofibrant-is-sharp)
        ( Y ∘ᶠᶠᵉ map-fibrant-replacement-is-sharp))
      ( map-coerce ∘ᵉᶠᵉ f ∘ᶠᶠᵉ map-fibrant-replacement-is-sharp)

  field
    is-equiv-precomp-is-sharp :
      ( Y : fibrant-replacement-is-sharp → UU j) →
      is-equiv (precomp-map-is-sharp Y)

open is-sharp public

Sharp-Type : (l1 l2 : Level) → UUᵉ (lsuc (l1 ⊔ l2))
Sharp-Type l1 l2 = Σᵉ (UUᵉ l1) (λ B → is-sharp B l2)

type-Sharp-Type : {l1 l2 : Level} → Sharp-Type l1 l2 → UUᵉ l1
type-Sharp-Type = pr1ᵉ

is-sharp-Sharp-Type :
  {l1 l2 : Level} (B : Sharp-Type l1 l2) →
  is-sharp (type-Sharp-Type B) l2
is-sharp-Sharp-Type = pr2ᵉ

is-cofibrant-Sharp-Type :
  {l1 l2 : Level} (B : Sharp-Type l1 l2) →
  is-cofibrant (type-Sharp-Type B) l2
is-cofibrant-Sharp-Type B =
  is-cofibrant-is-sharp (is-sharp-Sharp-Type B)

fibrant-replacement-Sharp-Type :
  {l1 l2 : Level} (B : Sharp-Type l1 l2) →
  UU l1
fibrant-replacement-Sharp-Type B =
  fibrant-replacement-is-sharp (is-sharp-Sharp-Type B)

map-fibrant-replacement-Sharp-Type :
  {l1 l2 : Level} (B : Sharp-Type l1 l2) →
  type-Sharp-Type B → fibrant-replacement-Sharp-Type B
map-fibrant-replacement-Sharp-Type B =
  map-fibrant-replacement-is-sharp (is-sharp-Sharp-Type B)
```

### Fibrant "equality" in sharp types

```agda
id-is-sharp :
  {l1 l2 : Level} {B : UUᵉ l1} →
  is-sharp B l2 → (x y : B) → UU l1
id-is-sharp is-sharp-B x y =
  map-fibrant-replacement-is-sharp is-sharp-B x ＝
  map-fibrant-replacement-is-sharp is-sharp-B y

id-Sharp-Type :
  {l1 l2 : Level} {B : Sharp-Type l1 l2}
  (x y : type-Sharp-Type B) → UU l1
id-Sharp-Type {B = B} = id-is-sharp (is-sharp-Sharp-Type B)
```

## Properties

### It is enough that the precomposition map is a section

```agda
is-sharp-precomp-section :
  {i : Level} (B : UUᵉ i) (j : Level) →
  (is-cofibrant-B : is-cofibrant B (i))
  (RB : UU i)
  (r : B → RB) →
  ((Y : RB → UU (i)) →
  section
    ( λ (f : Π RB Y) →
      ( map-inv-coerce
        ( map-inv-is-fibrant
          ( is-fibrant-Π-is-cofibrant is-cofibrant-B (Y ∘ᶠᶠᵉ r))
          ( map-coerce ∘ᵉᶠᵉ f ∘ᶠᶠᵉ r))))) →
  is-sharp B (i)
is-sharp-precomp-section {i} B j is-cofibrant-B RB r H =
  mk-is-sharp
    ( is-cofibrant-B)
    ( RB)
    ( r)
    ( λ Y →
      pair
        ( H Y)
        ( pair
          ( pr1 (H Y))
          ( λ f → lemma Y (pr1 (H Y) (α Y f)) f (pr2 (H Y) (α Y f)))))
  where
    module _ (Y : RB → UU (i)) where
      is-fibrant-Π-B = is-fibrant-Π-is-cofibrant is-cofibrant-B
      FM : UU (i)
      FM =
        witness-Fibrant-Type
          ( fibrant-Π-is-cofibrant is-cofibrant-B (Y ∘ᶠᶠᵉ r))
      α : Π RB Y → FM
      α f =
        witness-exotype-is-fibrant
          ( is-fibrant-Π-B (Y ∘ᶠᶠᵉ r))
          ( map-coerce ∘ᵉᶠᵉ f ∘ᶠᶠᵉ r)
      lemma : (f g : Π RB Y) → α f ＝ α g → f ＝ g
      lemma f g p =
        eq-htpy
          (pr1 (H (λ c → f c ＝ g c))
            ( witness-exotype-is-fibrant
              ( is-fibrant-Π-B ((λ c → f c ＝ g c) ∘ᶠᶠᵉ r))
              ( λ b →
                map-coerce
                  ( apᵐ
                    ( λ - → map-inv-coerce (- b))
                    ( invᵉ
                      ( is-retraction-map-is-fibrant
                        ( is-fibrant-Π-B (Y ∘ᶠᶠᵉ r))
                        ( λ b → map-coerce (f (r b)))))  ∙
                    ap
                      (λ - →
                        map-inv-coerce
                          ( exotype-witness-is-fibrant
                            (is-fibrant-Π-B (Y ∘ᶠᶠᵉ r)) - b)) p  ∙
                    apᵐ
                      ( λ - → map-inv-coerce (- b))
                      ( is-retraction-map-is-fibrant
                        ( is-fibrant-Π-B (Y ∘ᶠᶠᵉ r))
                        ( λ b → map-coerce (g (r b))))))))
```

### Closure under isos

```agda
is-sharp-equivᵉ :
  {l l' : Level} {A : UUᵉ l} {B : UUᵉ l} →
  is-sharp A l' → A ≃ᵉ B → is-sharp B l'
is-sharp-equivᵉ {l} {l'} {A} {B} is-sharp-A e =
  mk-is-sharp
    ( is-cofibrant-equivᵉ (is-cofibrant-is-sharp is-sharp-A) e)
    ( fibrant-replacement-is-sharp is-sharp-A)
    ( map-fibrant-replacement-is-sharp is-sharp-A ∘ᶠᵉᵉ map-inv-equivᵉ e)
    ( λ Y → 
      is-equiv-left-map-triangle _
        ( witness-exotype-Fibrant-Type
          ( fibrant-Π-is-cofibrant
            ( is-cofibrant-equivᵉ (is-cofibrant-is-sharp is-sharp-A) e)
            ( Y ∘ᶠᶠᵉ
              map-fibrant-replacement-is-sharp is-sharp-A ∘ᶠᵉᵉ
              map-inv-equivᵉ e)) ∘ᶠᵉᶠ
          ( _∘ᵉ map-inv-equivᵉ e) ∘ᵉᵉᶠ
          exotype-witness-Fibrant-Type
            ( fibrant-Π-is-cofibrant
              ( is-cofibrant-is-sharp is-sharp-A)
              ( Y ∘ᶠᶠᵉ map-fibrant-replacement-is-sharp is-sharp-A)))
        ( precomp-map-is-sharp is-sharp-A Y)
        ( λ f →
          apᵐ
            ( λ - → witness-exotype-Fibrant-Type (fibrant-Π-B Y) (φ Y -))
            ( invᵉ
              ( is-section-witness-exotype-Fibrant-Type
                ( fibrant-Π-A Y)
                ( α Y f))))
        ( is-equiv-precomp-is-sharp is-sharp-A Y)
        ( is-equiv-induced-map-hom-Fibrant-Type
          ( fibrant-Π-A Y)
          ( fibrant-Π-B Y)
          ( φ Y)
          ( is-equiv-precomp-Π-is-equivᵉ (is-equiv-map-inv-equivᵉ e) _)))
  where
    module _ (Y : fibrant-replacement-is-sharp is-sharp-A → UU l') where
      RA = fibrant-replacement-is-sharp is-sharp-A
      r = map-fibrant-replacement-is-sharp is-sharp-A
      α : Π RA Y → Πᵉ A (coerce ∘ᵉᶠᵉ Y ∘ᶠᶠᵉ r)
      α f = map-coerce ∘ᵉᶠᵉ f ∘ᶠᶠᵉ r
      fibrant-Π-A =
        fibrant-Π-is-cofibrant
          ( is-cofibrant-is-sharp is-sharp-A)
          ( Y ∘ᶠᶠᵉ map-fibrant-replacement-is-sharp is-sharp-A)
      fibrant-Π-B =
        fibrant-Π-is-cofibrant
          ( is-cofibrant-equivᵉ (is-cofibrant-is-sharp is-sharp-A) e)
          ( Y ∘ᶠᶠᵉ
            map-fibrant-replacement-is-sharp is-sharp-A ∘ᶠᵉᵉ
            map-inv-equivᵉ e)
      φ : type-Fibrant-Type fibrant-Π-A → type-Fibrant-Type fibrant-Π-B
      φ = _∘ᵉ map-inv-equivᵉ e
```

### Inner types are sharp

```agda
is-sharp-coerce :
 {l1 l2 : Level} (B : UU l1) → is-sharp (coerce B) l2
is-sharp-coerce B =
  mk-is-sharp
    ( is-cofibrant-coerce B)
    ( B)
    ( map-inv-coerce)
    ( λ Y → is-equiv-id)
```

### Fibrant types are sharp

```agda
is-sharp-is-fibrant :
 {l1 l2 : Level} {B : UUᵉ l1} → is-fibrant B → is-sharp B l2
is-sharp-is-fibrant is-fibrant-B =
   is-sharp-equivᵉ
     ( is-sharp-coerce (witness-is-fibrant is-fibrant-B))
     ( equiv-witness-is-fibrant is-fibrant-B)
```

### J for sharp types

```agda
-- J-is-sharp :
--   {l1 l2 : Level} {B : UUᵉ l1} →
--   (is-sharp-B : is-sharp B (l1 ⊔ lsuc l2))
--   (b : B) (Y : (y : B) → (id-is-sharp is-sharp-B b y) → UU l2) (d : Y b refl) →
--   (y : B) (p : id-is-sharp is-sharp-B b y) → Y y p
-- J-is-sharp {l1} {l2} {B} is-sharp-B b Y d y p = {!!}
--   where
--     FibrantΠ =
--       is-fibrant-Π-is-cofibrant
--         ( is-cofibrant-is-sharp is-sharp-B)
--         ( λ y → (id-is-sharp is-sharp-B b y) → UU l2)
--     test = {! is-equiv-precomp-is-sharp is-sharp-B (λ (x : RB) → (p : rb ＝ x) → Y ) !}

-- _-_ : ℕᵉ → ℕᵉ → ℕᵉ
-- 0ᵉ - 0ᵉ = 0ᵉ
-- 0ᵉ - succ-ℕᵉ n = 0ᵉ
-- succ-ℕᵉ m - 0ᵉ = succ-ℕᵉ m
-- succ-ℕᵉ m - succ-ℕᵉ n = m - n

-- record Foo (A : UUᵉ) (n : ℕᵉ) : UUᵉ where
--   inductive
--   field
--     elem     : A
--     subtrees : Foo A (n - 1ᵉ)

-- Foo :
--   (A : UUᵉ) (n : ℕᵉ) → UUᵉ
-- Foo A 0ᵉ = A
-- Foo A (succ-ℕᵉ n) = {!!}
--   where
--     record Test : UUᵉ where
--     field
--       test : Foo n
```
