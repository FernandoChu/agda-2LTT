# Universe levels

```agda
module foundation.universe-levelsᵉ where

open import Agda.Primitive
  using (Level ; lzero ; lsuc ; _⊔_)
  renaming (SSet to UUᵉ ; SSetω to UUωᵉ)
  public
```

## Idea

Weᵉ import Agda'sᵉ builtᵉ in mechanismᵉ ofᵉ universeᵉ levels.ᵉ Theᵉ universesᵉ areᵉ calledᵉ
`UU`,ᵉ whichᵉ standsᵉ forᵉ _univalentᵉ universe_,ᵉ althoughᵉ weᵉ willᵉ notᵉ immediatelyᵉ
assumeᵉ thatᵉ universesᵉ areᵉ univalent.ᵉ Thisᵉ isᵉ doneᵉ in
[foundation.univalence](foundation.univalence.md).ᵉ
