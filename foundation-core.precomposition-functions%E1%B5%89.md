# Precomposition of functions

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="foundation-core.precomposition-functions%25E1%25B5%2589.html" class="Module">foundation-core.precomposition-functionsᵉ</a> <a id="89" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="foundation-core.function-types%25E1%25B5%2589.html" class="Module">foundation-core.function-typesᵉ</a>
</pre>
</details>

## Idea

Given a function `f : A → B` and a type `X`, the **precomposition function** by
`f`

```text
  - ∘ f : (B → X) → (A → X)
```

is defined by `λ h x → h (f x)`.

## Definitions

### The precomposition operation on ordinary functions

<pre class="Agda"><a id="496" class="Keyword">module</a> <a id="503" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#503" class="Module">_</a>
  <a id="507" class="Symbol">{</a><a id="508" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#508" class="Bound">l1ᵉ</a> <a id="512" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#512" class="Bound">l2ᵉ</a> <a id="516" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#516" class="Bound">l3ᵉ</a> <a id="520" class="Symbol">:</a> <a id="522" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="527" class="Symbol">}</a> <a id="529" class="Symbol">{</a><a id="530" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#530" class="Bound">Aᵉ</a> <a id="533" class="Symbol">:</a> <a id="535" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="539" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#508" class="Bound">l1ᵉ</a><a id="542" class="Symbol">}</a> <a id="544" class="Symbol">{</a><a id="545" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#545" class="Bound">Bᵉ</a> <a id="548" class="Symbol">:</a> <a id="550" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="554" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#512" class="Bound">l2ᵉ</a><a id="557" class="Symbol">}</a> <a id="559" class="Symbol">(</a><a id="560" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#560" class="Bound">fᵉ</a> <a id="563" class="Symbol">:</a> <a id="565" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#530" class="Bound">Aᵉ</a> <a id="568" class="Symbol">→</a> <a id="570" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#545" class="Bound">Bᵉ</a><a id="572" class="Symbol">)</a> <a id="574" class="Symbol">(</a><a id="575" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#575" class="Bound">Cᵉ</a> <a id="578" class="Symbol">:</a> <a id="580" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="584" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#516" class="Bound">l3ᵉ</a><a id="587" class="Symbol">)</a>
  <a id="591" class="Keyword">where</a>

  <a id="600" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#600" class="Function">precompᵉ</a> <a id="609" class="Symbol">:</a> <a id="611" class="Symbol">(</a><a id="612" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#545" class="Bound">Bᵉ</a> <a id="615" class="Symbol">→</a> <a id="617" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#575" class="Bound">Cᵉ</a><a id="619" class="Symbol">)</a> <a id="621" class="Symbol">→</a> <a id="623" class="Symbol">(</a><a id="624" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#530" class="Bound">Aᵉ</a> <a id="627" class="Symbol">→</a> <a id="629" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#575" class="Bound">Cᵉ</a><a id="631" class="Symbol">)</a>
  <a id="635" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#600" class="Function">precompᵉ</a> <a id="644" class="Symbol">=</a> <a id="646" href="foundation-core.function-types%25E1%25B5%2589.html#476" class="Function Operator">_∘ᵉ</a> <a id="650" href="foundation-core.precomposition-functions%25E1%25B5%2589.html#560" class="Bound">fᵉ</a>
</pre>