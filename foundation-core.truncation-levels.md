# Truncation levels

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a> <a id="71" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="127" class="Keyword">open</a> <a id="132" class="Keyword">import</a> <a id="139" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The type of **truncation levels** is a type similar to the type of
[natural numbers](elementary-number-theory.natural-numbers.md), but starting the
count at -2, so that [sets](foundation-core.sets.md) have
[truncation](foundation-core.truncated-types.md) level 0.

## Definitions

### The type of truncation levels

<pre class="Agda"><a id="516" class="Keyword">data</a> <a id="𝕋"></a><a id="521" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a> <a id="523" class="Symbol">:</a> <a id="525" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="528" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="534" class="Keyword">where</a>
  <a id="𝕋.neg-two-𝕋"></a><a id="542" href="foundation-core.truncation-levels.html#542" class="InductiveConstructor">neg-two-𝕋</a> <a id="552" class="Symbol">:</a> <a id="554" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a>
  <a id="𝕋.succ-𝕋"></a><a id="558" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="565" class="Symbol">:</a> <a id="567" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a> <a id="569" class="Symbol">→</a> <a id="571" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a>
</pre>
### Aliases for common truncation levels

<pre class="Agda"><a id="neg-one-𝕋"></a><a id="628" href="foundation-core.truncation-levels.html#628" class="Function">neg-one-𝕋</a> <a id="638" class="Symbol">:</a> <a id="640" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a>
<a id="642" href="foundation-core.truncation-levels.html#628" class="Function">neg-one-𝕋</a> <a id="652" class="Symbol">=</a> <a id="654" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="661" href="foundation-core.truncation-levels.html#542" class="InductiveConstructor">neg-two-𝕋</a>

<a id="zero-𝕋"></a><a id="672" href="foundation-core.truncation-levels.html#672" class="Function">zero-𝕋</a> <a id="679" class="Symbol">:</a> <a id="681" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a>
<a id="683" href="foundation-core.truncation-levels.html#672" class="Function">zero-𝕋</a> <a id="690" class="Symbol">=</a> <a id="692" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="699" href="foundation-core.truncation-levels.html#628" class="Function">neg-one-𝕋</a>

<a id="one-𝕋"></a><a id="710" href="foundation-core.truncation-levels.html#710" class="Function">one-𝕋</a> <a id="716" class="Symbol">:</a> <a id="718" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a>
<a id="720" href="foundation-core.truncation-levels.html#710" class="Function">one-𝕋</a> <a id="726" class="Symbol">=</a> <a id="728" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="735" href="foundation-core.truncation-levels.html#672" class="Function">zero-𝕋</a>

<a id="two-𝕋"></a><a id="743" href="foundation-core.truncation-levels.html#743" class="Function">two-𝕋</a> <a id="749" class="Symbol">:</a> <a id="751" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a>
<a id="753" href="foundation-core.truncation-levels.html#743" class="Function">two-𝕋</a> <a id="759" class="Symbol">=</a> <a id="761" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="768" href="foundation-core.truncation-levels.html#710" class="Function">one-𝕋</a>
</pre>