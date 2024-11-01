# Families of equivalences

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="foundation.families-of-equivalences.html" class="Module">foundation.families-of-equivalences</a> <a id="80" class="Keyword">where</a>

<a id="87" class="Keyword">open</a> <a id="92" class="Keyword">import</a> <a id="99" href="foundation-core.families-of-equivalences.html" class="Module">foundation-core.families-of-equivalences</a> <a id="140" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="233" class="Keyword">open</a> <a id="238" class="Keyword">import</a> <a id="245" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

A **family of equivalences** is a family

```text
  eᵢ : A i ≃ B i
```

of [equivalences](foundation-core.equivalences.md). Families of equivalences are
also called **fiberwise equivalences**.

## Properties

### Being a fiberwise equivalence is a proposition

<pre class="Agda"><a id="609" class="Keyword">module</a> <a id="616" href="foundation.families-of-equivalences.html#616" class="Module">_</a>
  <a id="620" class="Symbol">{</a><a id="621" href="foundation.families-of-equivalences.html#621" class="Bound">l1</a> <a id="624" href="foundation.families-of-equivalences.html#624" class="Bound">l2</a> <a id="627" href="foundation.families-of-equivalences.html#627" class="Bound">l3</a> <a id="630" class="Symbol">:</a> <a id="632" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="637" class="Symbol">}</a> <a id="639" class="Symbol">{</a><a id="640" href="foundation.families-of-equivalences.html#640" class="Bound">A</a> <a id="642" class="Symbol">:</a> <a id="644" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="647" href="foundation.families-of-equivalences.html#621" class="Bound">l1</a><a id="649" class="Symbol">}</a> <a id="651" class="Symbol">{</a><a id="652" href="foundation.families-of-equivalences.html#652" class="Bound">B</a> <a id="654" class="Symbol">:</a> <a id="656" href="foundation.families-of-equivalences.html#640" class="Bound">A</a> <a id="658" class="Symbol">→</a> <a id="660" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="663" href="foundation.families-of-equivalences.html#624" class="Bound">l2</a><a id="665" class="Symbol">}</a> <a id="667" class="Symbol">{</a><a id="668" href="foundation.families-of-equivalences.html#668" class="Bound">C</a> <a id="670" class="Symbol">:</a> <a id="672" href="foundation.families-of-equivalences.html#640" class="Bound">A</a> <a id="674" class="Symbol">→</a> <a id="676" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="679" href="foundation.families-of-equivalences.html#627" class="Bound">l3</a><a id="681" class="Symbol">}</a>
  <a id="685" class="Keyword">where</a>

  <a id="694" href="foundation.families-of-equivalences.html#694" class="Function">is-property-is-fiberwise-equiv</a> <a id="725" class="Symbol">:</a>
    <a id="731" class="Symbol">(</a><a id="732" href="foundation.families-of-equivalences.html#732" class="Bound">f</a> <a id="734" class="Symbol">:</a> <a id="736" class="Symbol">(</a><a id="737" href="foundation.families-of-equivalences.html#737" class="Bound">a</a> <a id="739" class="Symbol">:</a> <a id="741" href="foundation.families-of-equivalences.html#640" class="Bound">A</a><a id="742" class="Symbol">)</a> <a id="744" class="Symbol">→</a> <a id="746" href="foundation.families-of-equivalences.html#652" class="Bound">B</a> <a id="748" href="foundation.families-of-equivalences.html#737" class="Bound">a</a> <a id="750" class="Symbol">→</a> <a id="752" href="foundation.families-of-equivalences.html#668" class="Bound">C</a> <a id="754" href="foundation.families-of-equivalences.html#737" class="Bound">a</a><a id="755" class="Symbol">)</a> <a id="757" class="Symbol">→</a> <a id="759" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="767" class="Symbol">(</a><a id="768" href="foundation-core.families-of-equivalences.html#710" class="Function">is-fiberwise-equiv</a> <a id="787" href="foundation.families-of-equivalences.html#732" class="Bound">f</a><a id="788" class="Symbol">)</a>
  <a id="792" href="foundation.families-of-equivalences.html#694" class="Function">is-property-is-fiberwise-equiv</a> <a id="823" href="foundation.families-of-equivalences.html#823" class="Bound">f</a> <a id="825" class="Symbol">=</a>
    <a id="831" href="foundation-core.propositions.html#5482" class="Function">is-prop-Π</a> <a id="841" class="Symbol">(λ</a> <a id="844" href="foundation.families-of-equivalences.html#844" class="Bound">a</a> <a id="846" class="Symbol">→</a> <a id="848" href="foundation.equivalences.html#4866" class="Function">is-property-is-equiv</a> <a id="869" class="Symbol">(</a><a id="870" href="foundation.families-of-equivalences.html#823" class="Bound">f</a> <a id="872" href="foundation.families-of-equivalences.html#844" class="Bound">a</a><a id="873" class="Symbol">))</a>
</pre>
## See also

- In
  [Functoriality of dependent pair types](foundation-core.functoriality-dependent-pair-types.md)
  we show that a family of maps is a fiberwise equivalence if and only if it
  induces an equivalence on [total spaces](foundation.dependent-pair-types.md).
