# Small types

<pre class="Agda"><a id="24" class="Keyword">module</a> <a id="31" href="foundation.small-types.html" class="Module">foundation.small-types</a> <a id="54" class="Keyword">where</a>

<a id="61" class="Keyword">open</a> <a id="66" class="Keyword">import</a> <a id="73" href="foundation-core.small-types.html" class="Module">foundation-core.small-types</a> <a id="101" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="158" class="Keyword">open</a> <a id="163" class="Keyword">import</a> <a id="170" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="202" class="Keyword">open</a> <a id="207" class="Keyword">import</a> <a id="214" href="foundation.images.html" class="Module">foundation.images</a>
<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="foundation.locally-small-types.html" class="Module">foundation.locally-small-types</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="foundation.replacement.html" class="Module">foundation.replacement</a>
<a id="310" class="Keyword">open</a> <a id="315" class="Keyword">import</a> <a id="322" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="349" class="Keyword">open</a> <a id="354" class="Keyword">import</a> <a id="361" href="foundation.uniqueness-image.html" class="Module">foundation.uniqueness-image</a>
<a id="389" class="Keyword">open</a> <a id="394" class="Keyword">import</a> <a id="401" href="foundation.universal-property-image.html" class="Module">foundation.universal-property-image</a>
<a id="437" class="Keyword">open</a> <a id="442" class="Keyword">import</a> <a id="449" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="477" class="Keyword">open</a> <a id="482" class="Keyword">import</a> <a id="489" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="516" class="Keyword">open</a> <a id="521" class="Keyword">import</a> <a id="528" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
</pre>
</details>

## Properties

### If `f` is a surjective map from a small type into a locally small type, then replacement implies that the codomain is small

<pre class="Agda"><a id="is-small-is-surjective"></a><a id="724" href="foundation.small-types.html#724" class="Function">is-small-is-surjective</a> <a id="747" class="Symbol">:</a>
  <a id="751" class="Symbol">{</a><a id="752" href="foundation.small-types.html#752" class="Bound">l1</a> <a id="755" href="foundation.small-types.html#755" class="Bound">l2</a> <a id="758" href="foundation.small-types.html#758" class="Bound">l3</a> <a id="761" class="Symbol">:</a> <a id="763" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="768" class="Symbol">}</a> <a id="770" class="Symbol">{</a><a id="771" href="foundation.small-types.html#771" class="Bound">A</a> <a id="773" class="Symbol">:</a> <a id="775" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="778" href="foundation.small-types.html#752" class="Bound">l1</a><a id="780" class="Symbol">}</a> <a id="782" class="Symbol">{</a><a id="783" href="foundation.small-types.html#783" class="Bound">B</a> <a id="785" class="Symbol">:</a> <a id="787" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="790" href="foundation.small-types.html#755" class="Bound">l2</a><a id="792" class="Symbol">}</a> <a id="794" class="Symbol">{</a><a id="795" href="foundation.small-types.html#795" class="Bound">f</a> <a id="797" class="Symbol">:</a> <a id="799" href="foundation.small-types.html#771" class="Bound">A</a> <a id="801" class="Symbol">→</a> <a id="803" href="foundation.small-types.html#783" class="Bound">B</a><a id="804" class="Symbol">}</a> <a id="806" class="Symbol">→</a>
  <a id="810" href="foundation.surjective-maps.html#2345" class="Function">is-surjective</a> <a id="824" href="foundation.small-types.html#795" class="Bound">f</a> <a id="826" class="Symbol">→</a> <a id="828" href="foundation-core.small-types.html#1212" class="Function">is-small</a> <a id="837" href="foundation.small-types.html#758" class="Bound">l3</a> <a id="840" href="foundation.small-types.html#771" class="Bound">A</a> <a id="842" class="Symbol">→</a> <a id="844" href="foundation.locally-small-types.html#1143" class="Function">is-locally-small</a> <a id="861" href="foundation.small-types.html#758" class="Bound">l3</a> <a id="864" href="foundation.small-types.html#783" class="Bound">B</a> <a id="866" class="Symbol">→</a>
  <a id="870" href="foundation-core.small-types.html#1212" class="Function">is-small</a> <a id="879" href="foundation.small-types.html#758" class="Bound">l3</a> <a id="882" href="foundation.small-types.html#783" class="Bound">B</a>
<a id="884" href="foundation.small-types.html#724" class="Function">is-small-is-surjective</a> <a id="907" class="Symbol">{</a><a id="908" class="Argument">f</a> <a id="910" class="Symbol">=</a> <a id="912" href="foundation.small-types.html#912" class="Bound">f</a><a id="913" class="Symbol">}</a> <a id="915" href="foundation.small-types.html#915" class="Bound">H</a> <a id="917" href="foundation.small-types.html#917" class="Bound">K</a> <a id="919" href="foundation.small-types.html#919" class="Bound">L</a> <a id="921" class="Symbol">=</a>
  <a id="925" href="foundation-core.small-types.html#3951" class="Function">is-small-equiv&#39;</a>
    <a id="945" class="Symbol">(</a> <a id="947" href="foundation.images.html#1490" class="Function">im</a> <a id="950" href="foundation.small-types.html#912" class="Bound">f</a><a id="951" class="Symbol">)</a>
    <a id="957" class="Symbol">(</a> <a id="959" href="foundation.uniqueness-image.html#8016" class="Function">equiv-equiv-slice-uniqueness-im</a> <a id="991" href="foundation.small-types.html#912" class="Bound">f</a> <a id="993" href="foundation-core.embeddings.html#2227" class="Function">id-emb</a>
      <a id="1006" class="Symbol">(</a> <a id="1008" href="foundation.small-types.html#912" class="Bound">f</a> <a id="1010" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1012" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="1021" class="Symbol">)</a>
      <a id="1029" class="Symbol">(</a> <a id="1031" href="foundation.universal-property-image.html#10805" class="Function">is-image-is-surjective</a> <a id="1054" href="foundation.small-types.html#912" class="Bound">f</a> <a id="1056" href="foundation-core.embeddings.html#2227" class="Function">id-emb</a> <a id="1063" class="Symbol">(</a><a id="1064" href="foundation.small-types.html#912" class="Bound">f</a> <a id="1066" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1068" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="1077" class="Symbol">)</a> <a id="1079" href="foundation.small-types.html#915" class="Bound">H</a><a id="1080" class="Symbol">))</a>
    <a id="1087" class="Symbol">(</a> <a id="1089" href="foundation.replacement.html#1103" class="Postulate">replacement</a> <a id="1101" href="foundation.small-types.html#912" class="Bound">f</a> <a id="1103" href="foundation.small-types.html#917" class="Bound">K</a> <a id="1105" href="foundation.small-types.html#919" class="Bound">L</a><a id="1106" class="Symbol">)</a>
</pre>
## See also

- [Small maps](foundation.small-maps.md)
