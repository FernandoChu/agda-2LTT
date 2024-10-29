# Sharp exo-types

```agda
module foundation.sharp-typesᵉ where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.unit-type

open import foundation.pi-decompositionsᵉ
open import foundation.pi-decompositions
open import foundation.action-on-identifications-functionsᵉ
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
    map-inv-coerce
      ( map-inv-is-fibrant
        ( pr1ᵉ is-cofibrant-is-sharp (Y ∘ᶠᶠᵉ map-fibrant-replacement-is-sharp))
        ( map-coerce ∘ᵉᶠᵉ f ∘ᶠᶠᵉ map-fibrant-replacement-is-sharp))

  precomp-map-is-sharp' :
    ( Y : fibrant-replacement-is-sharp → UU j) →
    ( Π fibrant-replacement-is-sharp Y) →
    witness-Fibrant-Type
      ( fibrant-Π-is-cofibrant is-cofibrant-is-sharp
        ( Y ∘ᶠᶠᵉ map-fibrant-replacement-is-sharp))
  precomp-map-is-sharp' Y = 
    induced-map-hom-Fibrant-Type
      ( Π-Fibrant-Type (Fibrant-Type-coerce fibrant-replacement-is-sharp) (λ a → Fibrant-Type-coerce (Y (map-inv-coerce a))))
      ( fibrant-Π-is-cofibrant
        ( is-cofibrant-is-sharp)
        ( Y ∘ᶠᶠᵉ map-fibrant-replacement-is-sharp))
       λ h → h ∘ᵉ map-coerce ∘ᵉᶠᵉ map-fibrant-replacement-is-sharp

   -- ( induced-map-hom-Fibrant-Type
   --    ( Π-Fibrant-Type fibrant-replacement-is-sharp Y)
   --    ( fibrant-Π-is-cofibrant
   --      ( is-cofibrant-is-sharp)
   --      ( Y ∘ᵉ map-fibrant-replacement-is-sharp))
   --    ( λ h → h ∘ᵉ map-fibrant-replacement-is-sharp))

  field
    is-equiv-precomp-is-sharp :
      ( Y : fibrant-replacement-is-sharp → UU j) →
      is-equiv (precomp-map-is-sharp Y)

open is-sharp public
```

### Properties

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
          ( pr1ᵉ is-cofibrant-B (Y ∘ᶠᶠᵉ r))
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
      FM : UU (i)
      FM =
        witness-Fibrant-Type
          ( fibrant-Π-is-cofibrant is-cofibrant-B (Y ∘ᶠᶠᵉ r))
      α : Π RB Y → FM
      α f =
        witness-exotype-is-fibrant
          ( pr1ᵉ is-cofibrant-B (Y ∘ᶠᶠᵉ r))
          ( map-coerce ∘ᵉᶠᵉ f ∘ᶠᶠᵉ r)
      lemma : (f g : Π RB Y) → α f ＝ α g → f ＝ g
      lemma f g p =
        eq-htpy
          (pr1 (H (λ c → f c ＝ g c))
            ( witness-exotype-is-fibrant
              ( pr1ᵉ is-cofibrant-B ((λ c → f c ＝ g c) ∘ᶠᶠᵉ r))
              ( λ b →
                map-coerce
                  ( apᵐ
                    ( λ - → map-inv-coerce (- b))
                    ( invᵉ
                      ( is-retraction-map-is-fibrant
                        ( pr1ᵉ is-cofibrant-B (Y ∘ᶠᶠᵉ r))
                        ( λ b → map-coerce (f (r b)))))  ∙
                    ap
                      (λ - →
                        map-inv-coerce
                          ( exotype-witness-is-fibrant
                            (pr1ᵉ is-cofibrant-B (Y ∘ᶠᶠᵉ r)) - b)) p  ∙
                    apᵐ
                      ( λ - → map-inv-coerce (- b))
                      ( is-retraction-map-is-fibrant
                        ( pr1ᵉ is-cofibrant-B (Y ∘ᶠᶠᵉ r))
                        ( λ b → map-coerce (g (r b))))))))
```
