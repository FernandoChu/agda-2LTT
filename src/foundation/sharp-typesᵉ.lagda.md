# Sharp exo-types

```agda
module foundation.sharp-typesᵉ where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.unit-type

open import foundation.pi-decompositionsᵉ
open import foundation.cofibrant-typesᵉ
open import foundation.fibrant-typesᵉ
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.function-typesᵉ
open import foundation.function-types
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
```

## Idea

## Definition

### Sharp types

```agda
record is-sharp {i : Level} (B : UUᵉ i) (j : Level) : UUᵉ (lsuc (i ⊔ j)) where
  field
    is-cofibrant-is-sharp : is-cofibrant B j
    fibrant-replacement-is-sharp : Fibrant-Type i
    map-fibrant-replacement-is-sharp : B → type-Fibrant-Type fibrant-replacement-is-sharp

  precomp-map-is-sharp :
    ( Y : type-Fibrant-Type fibrant-replacement-is-sharp → Fibrant-Type j) →
    witness-Fibrant-Type
      ( Π-Fibrant-Type fibrant-replacement-is-sharp Y) →
    witness-Fibrant-Type
      ( fibrant-Π-is-cofibrant is-cofibrant-is-sharp
        ( Y ∘ᵉ map-fibrant-replacement-is-sharp))
  precomp-map-is-sharp Y =
    ( induced-map-hom-Fibrant-Type
      ( Π-Fibrant-Type fibrant-replacement-is-sharp Y)
      ( fibrant-Π-is-cofibrant
        ( is-cofibrant-is-sharp)
        ( Y ∘ᵉ map-fibrant-replacement-is-sharp))
      ( λ h → h ∘ᵉ map-fibrant-replacement-is-sharp))

  field
    is-equiv-precomp-is-sharp :
      ( Y : type-Fibrant-Type fibrant-replacement-is-sharp → Fibrant-Type j) →
      is-equiv (precomp-map-is-sharp Y)

open is-sharp public
```

### Properties

```agda
is-section-precomp-is-sharp :
  {i : Level} (B : UUᵉ i) (j : Level) →
  (B# : is-sharp B j) →
  (Y : type-Fibrant-Type (fibrant-replacement-is-sharp B#) → Fibrant-Type j) →
  section (precomp-map-is-sharp B# Y)
is-section-precomp-is-sharp B j B# Y =
  section-is-equiv (is-equiv-precomp-is-sharp B# Y)

arst :
  {i : Level} (B : UUᵉ i) (j : Level) →
  (is-cofibrant-B : is-cofibrant B (i ⊔ j))
  (RB : Fibrant-Type i)
  (r : B → type-Fibrant-Type RB) →
  ((Z : Fibrant-Type (i ⊔ j)) →
  section
    ( induced-map-hom-Fibrant-Type
      ( Π-Fibrant-Type RB (λ _ → Z))
      (  fibrant-Π-is-cofibrant
        ( is-cofibrant-B)
        ( λ _ → Z) )
      ( λ h → h ∘ᵉ r))) →
  ((Y : type-Fibrant-Type RB → Fibrant-Type (i ⊔ j)) →
  section
    ( induced-map-hom-Fibrant-Type
      ( Π-Fibrant-Type RB Y)
      (  fibrant-Π-is-cofibrant
        ( is-cofibrant-B)
        ( Y ∘ᵉ r) )
      ( λ h → h ∘ᵉ r)))
pr1 (arst {i} B j is-cofibrant-B RB r H Y) f = {!!}
  where
    Z =
      Σ (witness-Fibrant-Type RB)
        ( λ c → witness-Fibrant-Type (Y (map-Fibrant-Type RB (map-coerce c))))
    fZ : Fibrant-Type (i ⊔ j)
    fZ = (coerce Z ,ᵉ mk-is-fibrant Z id-equivᵉ)
    σ : witness-Fibrant-Type
         (fibrant-Π-is-cofibrant is-cofibrant-B (λ _ → fZ)) →
         witness-Fibrant-Type (Π-Fibrant-Type RB (λ _ → fZ))
    σ = pr1 (H fZ)
    -- test : witness-Fibrant-Type (Π-Fibrant-Type RB (λ _ → fZ)) ＝ᵉ type-Fibrant-Type RB → type-Fibrant-Type fZ
    -- test = _
    f' : B → Z
    f' b =
      map-inv-coerce (map-inv-Fibrant-Type RB (r b)) ,
      lemma
        ( invᵉ (is-retraction-map-Fibrant-Type RB (r b)))
        ( map-inv-coerce
          ( map-inv-Fibrant-Type
            ( Y (r b))
            ( map-Fibrant-Type
              ( fibrant-Π-is-cofibrant is-cofibrant-B (Y ∘ᵉ r))
              ( map-coerce f)
              ( b))))
      where
        lemma :
          {a b : type-Fibrant-Type RB} → a ＝ᵉ b →
          witness-Fibrant-Type (Y a) → witness-Fibrant-Type (Y b)
        lemma reflᵉ p = p

pr2 (arst B j is-cofibrant-B RB r H Y) = {!!}

is-sharp-is-fibrant :
 {l1 l2 : Level} {A : UUᵉ l1} → is-fibrant A → is-sharp A l2
is-cofibrant-is-sharp (is-sharp-is-fibrant is-fibrant-A) =
  is-cofibrant-is-fibrant is-fibrant-A
fibrant-replacement-is-sharp (is-sharp-is-fibrant {A = A} is-fibrant-A) =
  (A ,ᵉ is-fibrant-A)
map-fibrant-replacement-is-sharp (is-sharp-is-fibrant is-fibrant-A) = idᵉ
is-equiv-precomp-is-sharp (is-sharp-is-fibrant {A = A} is-fibrant-A) Y =
  is-equiv-id-induced-map-hom-Fibrant-Type
    ((a : A) → type-Fibrant-Type (Y a))
    (is-fibrant-Fibrant-Type (Π-Fibrant-Type (A ,ᵉ is-fibrant-A) Y))
    (is-fibrant-Fibrant-Type (fibrant-Π-is-cofibrant (is-cofibrant-is-fibrant is-fibrant-A) Y) )
```
