# Discrete types

<pre class="Agda"><a id="27" class="Keyword">module</a> <a id="34" href="foundation-core.discrete-types.html" class="Module">foundation-core.discrete-types</a> <a id="65" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="121" class="Keyword">open</a> <a id="126" class="Keyword">import</a> <a id="133" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a>
<a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="207" class="Keyword">open</a> <a id="212" class="Keyword">import</a> <a id="219" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation-core.sets.html" class="Module">foundation-core.sets</a>
</pre>
</details>

## Idea

A {{#concept "discrete type" Agda=Discrete-Type}} is a type that has
[decidable equality](foundation.decidable-equality.md). Consequently, discrete
types are [sets](foundation-core.sets.md) by Hedberg's theorem.

## Definition

<pre class="Agda"><a id="Discrete-Type"></a><a id="542" href="foundation-core.discrete-types.html#542" class="Function">Discrete-Type</a> <a id="556" class="Symbol">:</a> <a id="558" class="Symbol">(</a><a id="559" href="foundation-core.discrete-types.html#559" class="Bound">l</a> <a id="561" class="Symbol">:</a> <a id="563" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="568" class="Symbol">)</a> <a id="570" class="Symbol">→</a> <a id="572" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="575" class="Symbol">(</a><a id="576" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="581" href="foundation-core.discrete-types.html#559" class="Bound">l</a><a id="582" class="Symbol">)</a>
<a id="584" href="foundation-core.discrete-types.html#542" class="Function">Discrete-Type</a> <a id="598" href="foundation-core.discrete-types.html#598" class="Bound">l</a> <a id="600" class="Symbol">=</a> <a id="602" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="604" class="Symbol">(</a><a id="605" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="608" href="foundation-core.discrete-types.html#598" class="Bound">l</a><a id="609" class="Symbol">)</a> <a id="611" href="foundation.decidable-equality.html#1268" class="Function">has-decidable-equality</a>

<a id="635" class="Keyword">module</a> <a id="642" href="foundation-core.discrete-types.html#642" class="Module">_</a>
  <a id="646" class="Symbol">{</a><a id="647" href="foundation-core.discrete-types.html#647" class="Bound">l</a> <a id="649" class="Symbol">:</a> <a id="651" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="656" class="Symbol">}</a> <a id="658" class="Symbol">(</a><a id="659" href="foundation-core.discrete-types.html#659" class="Bound">X</a> <a id="661" class="Symbol">:</a> <a id="663" href="foundation-core.discrete-types.html#542" class="Function">Discrete-Type</a> <a id="677" href="foundation-core.discrete-types.html#647" class="Bound">l</a><a id="678" class="Symbol">)</a>
  <a id="682" class="Keyword">where</a>

  <a id="691" href="foundation-core.discrete-types.html#691" class="Function">type-Discrete-Type</a> <a id="710" class="Symbol">:</a> <a id="712" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="715" href="foundation-core.discrete-types.html#647" class="Bound">l</a>
  <a id="719" href="foundation-core.discrete-types.html#691" class="Function">type-Discrete-Type</a> <a id="738" class="Symbol">=</a> <a id="740" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="744" href="foundation-core.discrete-types.html#659" class="Bound">X</a>

  <a id="749" href="foundation-core.discrete-types.html#749" class="Function">has-decidable-equality-type-Discrete-Type</a> <a id="791" class="Symbol">:</a>
    <a id="797" href="foundation.decidable-equality.html#1268" class="Function">has-decidable-equality</a> <a id="820" href="foundation-core.discrete-types.html#691" class="Function">type-Discrete-Type</a>
  <a id="841" href="foundation-core.discrete-types.html#749" class="Function">has-decidable-equality-type-Discrete-Type</a> <a id="883" class="Symbol">=</a> <a id="885" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="889" href="foundation-core.discrete-types.html#659" class="Bound">X</a>

  <a id="894" href="foundation-core.discrete-types.html#894" class="Function">is-set-type-Discrete-Type</a> <a id="920" class="Symbol">:</a> <a id="922" href="foundation-core.sets.html#795" class="Function">is-set</a> <a id="929" href="foundation-core.discrete-types.html#691" class="Function">type-Discrete-Type</a>
  <a id="950" href="foundation-core.discrete-types.html#894" class="Function">is-set-type-Discrete-Type</a> <a id="976" class="Symbol">=</a>
    <a id="982" href="foundation.decidable-equality.html#6553" class="Function">is-set-has-decidable-equality</a> <a id="1012" href="foundation-core.discrete-types.html#749" class="Function">has-decidable-equality-type-Discrete-Type</a>

  <a id="1057" href="foundation-core.discrete-types.html#1057" class="Function">set-Discrete-Type</a> <a id="1075" class="Symbol">:</a> <a id="1077" href="foundation-core.sets.html#870" class="Function">Set</a> <a id="1081" href="foundation-core.discrete-types.html#647" class="Bound">l</a>
  <a id="1085" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1089" href="foundation-core.discrete-types.html#1057" class="Function">set-Discrete-Type</a> <a id="1107" class="Symbol">=</a> <a id="1109" href="foundation-core.discrete-types.html#691" class="Function">type-Discrete-Type</a>
  <a id="1130" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1134" href="foundation-core.discrete-types.html#1057" class="Function">set-Discrete-Type</a> <a id="1152" class="Symbol">=</a> <a id="1154" href="foundation-core.discrete-types.html#894" class="Function">is-set-type-Discrete-Type</a>
</pre>
## External links

- [classical set](https://ncatlab.org/nlab/show/classical+set) at $n$Lab
- [decidable object](https://ncatlab.org/nlab/show/decidable+object) at $n$Lab
