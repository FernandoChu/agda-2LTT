# agda-2LTT

WIP of 2LTT using the [agda-unimath](https://github.com/UniMath/agda-unimath)
library.

## Installation

```
$ git clone --recurse-submodules git@github.com:FernandoChu/agda-2LTT.git
```

## Formalization notes

We allow ourselves to use `Σ` and `Π` types mixing both the inner and outer level, despite this not being considered in the original paper. This could be understood as an implicit coercion of the inner types.

Some definitions, such as being cofibrant or sharp, require some data about fibrant types. When it makes sense, we will instead change the definition to be about (coerced) inner types. This won't change anything, since everything is stable under isomorphism, but explicitely carrying this isomorphim around is extremely tedious and difficult to manage. The *Univalence Principle* seems to do this implicitely.
