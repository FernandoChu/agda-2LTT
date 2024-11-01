# Postcomposition of functions

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html" class="Module">foundation-core.postcomposition-functionsᵉ</a> <a id="91" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="147" class="Keyword">open</a> <a id="152" class="Keyword">import</a> <a id="159" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html" class="Module">foundation-core.postcomposition-dependent-functionsᵉ</a>
</pre>
</details>

## Idea

Given a map `f : X → Y` and a type `A`, the
{{#concept "postcomposition function" Agda=postcomp}}

```text
  f ∘ - : (A → X) → (A → Y)
```

is defined by `λ h x → f (h x)`.

## Definitions

<pre class="Agda"><a id="477" class="Keyword">module</a> <a id="484" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#484" class="Module">_</a>
  <a id="488" class="Symbol">{</a><a id="489" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#489" class="Bound">l1ᵉ</a> <a id="493" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#493" class="Bound">l2ᵉ</a> <a id="497" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#497" class="Bound">l3ᵉ</a> <a id="501" class="Symbol">:</a> <a id="503" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="508" class="Symbol">}</a> <a id="510" class="Symbol">(</a><a id="511" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#511" class="Bound">Aᵉ</a> <a id="514" class="Symbol">:</a> <a id="516" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="520" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#489" class="Bound">l1ᵉ</a><a id="523" class="Symbol">)</a> <a id="525" class="Symbol">{</a><a id="526" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#526" class="Bound">Xᵉ</a> <a id="529" class="Symbol">:</a> <a id="531" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="535" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#493" class="Bound">l2ᵉ</a><a id="538" class="Symbol">}</a> <a id="540" class="Symbol">{</a><a id="541" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#541" class="Bound">Yᵉ</a> <a id="544" class="Symbol">:</a> <a id="546" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="550" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#497" class="Bound">l3ᵉ</a><a id="553" class="Symbol">}</a>
  <a id="557" class="Keyword">where</a>

  <a id="566" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#566" class="Function">postcompᵉ</a> <a id="576" class="Symbol">:</a> <a id="578" class="Symbol">(</a><a id="579" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#526" class="Bound">Xᵉ</a> <a id="582" class="Symbol">→</a> <a id="584" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#541" class="Bound">Yᵉ</a><a id="586" class="Symbol">)</a> <a id="588" class="Symbol">→</a> <a id="590" class="Symbol">(</a><a id="591" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#511" class="Bound">Aᵉ</a> <a id="594" class="Symbol">→</a> <a id="596" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#526" class="Bound">Xᵉ</a><a id="598" class="Symbol">)</a> <a id="600" class="Symbol">→</a> <a id="602" class="Symbol">(</a><a id="603" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#511" class="Bound">Aᵉ</a> <a id="606" class="Symbol">→</a> <a id="608" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#541" class="Bound">Yᵉ</a><a id="610" class="Symbol">)</a>
  <a id="614" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#566" class="Function">postcompᵉ</a> <a id="624" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#624" class="Bound">fᵉ</a> <a id="627" class="Symbol">=</a> <a id="629" href="foundation-core.postcomposition-dependent-functions%25E1%25B5%2589.html#1382" class="Function">postcomp-Πᵉ</a> <a id="641" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#511" class="Bound">Aᵉ</a> <a id="644" href="foundation-core.postcomposition-functions%25E1%25B5%2589.html#624" class="Bound">fᵉ</a>
</pre>