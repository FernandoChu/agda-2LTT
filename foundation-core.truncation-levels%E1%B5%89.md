# Truncation levels

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="foundation-core.truncation-levels%25E1%25B5%2589.html" class="Module">foundation-core.truncation-levelsᵉ</a> <a id="72" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="128" class="Keyword">open</a> <a id="133" class="Keyword">import</a> <a id="140" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

The type of **truncation levels** is a type similar to the type of
[natural numbers](elementary-number-theory.natural-numbers.md), but starting the
count at -2, so that [sets](foundation-core.sets.md) have
[truncation](foundation-core.truncated-types.md) level 0.

## Definitions

### The type of truncation levels

<pre class="Agda"><a id="518" class="Keyword">data</a> <a id="𝕋ᵉ"></a><a id="523" href="foundation-core.truncation-levels%25E1%25B5%2589.html#523" class="Datatype">𝕋ᵉ</a> <a id="526" class="Symbol">:</a> <a id="528" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="532" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="538" class="Keyword">where</a>
  <a id="𝕋ᵉ.neg-two-𝕋ᵉ"></a><a id="546" href="foundation-core.truncation-levels%25E1%25B5%2589.html#546" class="InductiveConstructor">neg-two-𝕋ᵉ</a> <a id="557" class="Symbol">:</a> <a id="559" href="foundation-core.truncation-levels%25E1%25B5%2589.html#523" class="Datatype">𝕋ᵉ</a>
  <a id="𝕋ᵉ.succ-𝕋ᵉ"></a><a id="564" href="foundation-core.truncation-levels%25E1%25B5%2589.html#564" class="InductiveConstructor">succ-𝕋ᵉ</a> <a id="572" class="Symbol">:</a> <a id="574" href="foundation-core.truncation-levels%25E1%25B5%2589.html#523" class="Datatype">𝕋ᵉ</a> <a id="577" class="Symbol">→</a> <a id="579" href="foundation-core.truncation-levels%25E1%25B5%2589.html#523" class="Datatype">𝕋ᵉ</a>
</pre>
### Aliases for common truncation levels

<pre class="Agda"><a id="neg-one-𝕋ᵉ"></a><a id="637" href="foundation-core.truncation-levels%25E1%25B5%2589.html#637" class="Function">neg-one-𝕋ᵉ</a> <a id="648" class="Symbol">:</a> <a id="650" href="foundation-core.truncation-levels%25E1%25B5%2589.html#523" class="Datatype">𝕋ᵉ</a>
<a id="653" href="foundation-core.truncation-levels%25E1%25B5%2589.html#637" class="Function">neg-one-𝕋ᵉ</a> <a id="664" class="Symbol">=</a> <a id="666" href="foundation-core.truncation-levels%25E1%25B5%2589.html#564" class="InductiveConstructor">succ-𝕋ᵉ</a> <a id="674" href="foundation-core.truncation-levels%25E1%25B5%2589.html#546" class="InductiveConstructor">neg-two-𝕋ᵉ</a>

<a id="zero-𝕋ᵉ"></a><a id="686" href="foundation-core.truncation-levels%25E1%25B5%2589.html#686" class="Function">zero-𝕋ᵉ</a> <a id="694" class="Symbol">:</a> <a id="696" href="foundation-core.truncation-levels%25E1%25B5%2589.html#523" class="Datatype">𝕋ᵉ</a>
<a id="699" href="foundation-core.truncation-levels%25E1%25B5%2589.html#686" class="Function">zero-𝕋ᵉ</a> <a id="707" class="Symbol">=</a> <a id="709" href="foundation-core.truncation-levels%25E1%25B5%2589.html#564" class="InductiveConstructor">succ-𝕋ᵉ</a> <a id="717" href="foundation-core.truncation-levels%25E1%25B5%2589.html#637" class="Function">neg-one-𝕋ᵉ</a>

<a id="one-𝕋ᵉ"></a><a id="729" href="foundation-core.truncation-levels%25E1%25B5%2589.html#729" class="Function">one-𝕋ᵉ</a> <a id="736" class="Symbol">:</a> <a id="738" href="foundation-core.truncation-levels%25E1%25B5%2589.html#523" class="Datatype">𝕋ᵉ</a>
<a id="741" href="foundation-core.truncation-levels%25E1%25B5%2589.html#729" class="Function">one-𝕋ᵉ</a> <a id="748" class="Symbol">=</a> <a id="750" href="foundation-core.truncation-levels%25E1%25B5%2589.html#564" class="InductiveConstructor">succ-𝕋ᵉ</a> <a id="758" href="foundation-core.truncation-levels%25E1%25B5%2589.html#686" class="Function">zero-𝕋ᵉ</a>

<a id="two-𝕋ᵉ"></a><a id="767" href="foundation-core.truncation-levels%25E1%25B5%2589.html#767" class="Function">two-𝕋ᵉ</a> <a id="774" class="Symbol">:</a> <a id="776" href="foundation-core.truncation-levels%25E1%25B5%2589.html#523" class="Datatype">𝕋ᵉ</a>
<a id="779" href="foundation-core.truncation-levels%25E1%25B5%2589.html#767" class="Function">two-𝕋ᵉ</a> <a id="786" class="Symbol">=</a> <a id="788" href="foundation-core.truncation-levels%25E1%25B5%2589.html#564" class="InductiveConstructor">succ-𝕋ᵉ</a> <a id="796" href="foundation-core.truncation-levels%25E1%25B5%2589.html#729" class="Function">one-𝕋ᵉ</a>
</pre>