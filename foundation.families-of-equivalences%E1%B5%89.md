# Families of equivalences

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="foundation.families-of-equivalences%25E1%25B5%2589.html" class="Module">foundation.families-of-equivalencesᵉ</a> <a id="81" class="Keyword">where</a>

<a id="88" class="Keyword">open</a> <a id="93" class="Keyword">import</a> <a id="100" href="foundation-core.families-of-equivalences%25E1%25B5%2589.html" class="Module">foundation-core.families-of-equivalencesᵉ</a> <a id="142" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation.equivalences%25E1%25B5%2589.html" class="Module">foundation.equivalencesᵉ</a>
<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="foundation-core.propositions%25E1%25B5%2589.html" class="Module">foundation-core.propositionsᵉ</a>
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

<pre class="Agda"><a id="614" class="Keyword">module</a> <a id="621" href="foundation.families-of-equivalences%25E1%25B5%2589.html#621" class="Module">_</a>
  <a id="625" class="Symbol">{</a><a id="626" href="foundation.families-of-equivalences%25E1%25B5%2589.html#626" class="Bound">l1ᵉ</a> <a id="630" href="foundation.families-of-equivalences%25E1%25B5%2589.html#630" class="Bound">l2ᵉ</a> <a id="634" href="foundation.families-of-equivalences%25E1%25B5%2589.html#634" class="Bound">l3ᵉ</a> <a id="638" class="Symbol">:</a> <a id="640" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="645" class="Symbol">}</a> <a id="647" class="Symbol">{</a><a id="648" href="foundation.families-of-equivalences%25E1%25B5%2589.html#648" class="Bound">Aᵉ</a> <a id="651" class="Symbol">:</a> <a id="653" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="657" href="foundation.families-of-equivalences%25E1%25B5%2589.html#626" class="Bound">l1ᵉ</a><a id="660" class="Symbol">}</a> <a id="662" class="Symbol">{</a><a id="663" href="foundation.families-of-equivalences%25E1%25B5%2589.html#663" class="Bound">Bᵉ</a> <a id="666" class="Symbol">:</a> <a id="668" href="foundation.families-of-equivalences%25E1%25B5%2589.html#648" class="Bound">Aᵉ</a> <a id="671" class="Symbol">→</a> <a id="673" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="677" href="foundation.families-of-equivalences%25E1%25B5%2589.html#630" class="Bound">l2ᵉ</a><a id="680" class="Symbol">}</a> <a id="682" class="Symbol">{</a><a id="683" href="foundation.families-of-equivalences%25E1%25B5%2589.html#683" class="Bound">Cᵉ</a> <a id="686" class="Symbol">:</a> <a id="688" href="foundation.families-of-equivalences%25E1%25B5%2589.html#648" class="Bound">Aᵉ</a> <a id="691" class="Symbol">→</a> <a id="693" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="697" href="foundation.families-of-equivalences%25E1%25B5%2589.html#634" class="Bound">l3ᵉ</a><a id="700" class="Symbol">}</a>
  <a id="704" class="Keyword">where</a>

  <a id="713" href="foundation.families-of-equivalences%25E1%25B5%2589.html#713" class="Function">is-property-is-fiberwise-equivᵉ</a> <a id="745" class="Symbol">:</a>
    <a id="751" class="Symbol">(</a><a id="752" href="foundation.families-of-equivalences%25E1%25B5%2589.html#752" class="Bound">fᵉ</a> <a id="755" class="Symbol">:</a> <a id="757" class="Symbol">(</a><a id="758" href="foundation.families-of-equivalences%25E1%25B5%2589.html#758" class="Bound">aᵉ</a> <a id="761" class="Symbol">:</a> <a id="763" href="foundation.families-of-equivalences%25E1%25B5%2589.html#648" class="Bound">Aᵉ</a><a id="765" class="Symbol">)</a> <a id="767" class="Symbol">→</a> <a id="769" href="foundation.families-of-equivalences%25E1%25B5%2589.html#663" class="Bound">Bᵉ</a> <a id="772" href="foundation.families-of-equivalences%25E1%25B5%2589.html#758" class="Bound">aᵉ</a> <a id="775" class="Symbol">→</a> <a id="777" href="foundation.families-of-equivalences%25E1%25B5%2589.html#683" class="Bound">Cᵉ</a> <a id="780" href="foundation.families-of-equivalences%25E1%25B5%2589.html#758" class="Bound">aᵉ</a><a id="782" class="Symbol">)</a> <a id="784" class="Symbol">→</a> <a id="786" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="795" class="Symbol">(</a><a id="796" href="foundation-core.families-of-equivalences%25E1%25B5%2589.html#729" class="Function">is-fiberwise-equivᵉ</a> <a id="816" href="foundation.families-of-equivalences%25E1%25B5%2589.html#752" class="Bound">fᵉ</a><a id="818" class="Symbol">)</a>
  <a id="822" href="foundation.families-of-equivalences%25E1%25B5%2589.html#713" class="Function">is-property-is-fiberwise-equivᵉ</a> <a id="854" href="foundation.families-of-equivalences%25E1%25B5%2589.html#854" class="Bound">fᵉ</a> <a id="857" class="Symbol">=</a>
    <a id="863" href="foundation-core.propositions%25E1%25B5%2589.html#5919" class="Function">is-prop-Πᵉ</a> <a id="874" class="Symbol">(λ</a> <a id="877" href="foundation.families-of-equivalences%25E1%25B5%2589.html#877" class="Bound">aᵉ</a> <a id="880" class="Symbol">→</a> <a id="882" href="foundation.equivalences%25E1%25B5%2589.html#5065" class="Function">is-property-is-equivᵉ</a> <a id="904" class="Symbol">(</a><a id="905" href="foundation.families-of-equivalences%25E1%25B5%2589.html#854" class="Bound">fᵉ</a> <a id="908" href="foundation.families-of-equivalences%25E1%25B5%2589.html#877" class="Bound">aᵉ</a><a id="910" class="Symbol">))</a>
</pre>
## See also

- In
  [Functoriality of dependent pair types](foundation-core.functoriality-dependent-pair-types.md)
  we show that a family of maps is a fiberwise equivalence if and only if it
  induces an equivalence on [total spaces](foundation.dependent-pair-types.md).