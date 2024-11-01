# Cartesian product types

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html" class="Module">foundation-core.cartesian-product-typesᵉ</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Definitions

Cartesian products of types are defined as dependent pair types, using a
constant type family.

### The cartesian product type

<pre class="Agda"><a id="productᵉ"></a><a id="394" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#394" class="Function">productᵉ</a> <a id="403" class="Symbol">:</a> <a id="405" class="Symbol">{</a><a id="406" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#406" class="Bound">l1ᵉ</a> <a id="410" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#410" class="Bound">l2ᵉ</a> <a id="414" class="Symbol">:</a> <a id="416" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="421" class="Symbol">}</a> <a id="423" class="Symbol">(</a><a id="424" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#424" class="Bound">Aᵉ</a> <a id="427" class="Symbol">:</a> <a id="429" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="433" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#406" class="Bound">l1ᵉ</a><a id="436" class="Symbol">)</a> <a id="438" class="Symbol">(</a><a id="439" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#439" class="Bound">Bᵉ</a> <a id="442" class="Symbol">:</a> <a id="444" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="448" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#410" class="Bound">l2ᵉ</a><a id="451" class="Symbol">)</a> <a id="453" class="Symbol">→</a> <a id="455" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="459" class="Symbol">(</a><a id="460" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#406" class="Bound">l1ᵉ</a> <a id="464" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="466" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#410" class="Bound">l2ᵉ</a><a id="469" class="Symbol">)</a>
<a id="471" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#394" class="Function">productᵉ</a> <a id="480" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#480" class="Bound">Aᵉ</a> <a id="483" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#483" class="Bound">Bᵉ</a> <a id="486" class="Symbol">=</a> <a id="488" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="491" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#480" class="Bound">Aᵉ</a> <a id="494" class="Symbol">(λ</a> <a id="497" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#497" class="Bound">_</a> <a id="499" class="Symbol">→</a> <a id="501" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#483" class="Bound">Bᵉ</a><a id="503" class="Symbol">)</a>

<a id="pair&#39;ᵉ"></a><a id="506" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#506" class="Function">pair&#39;ᵉ</a> <a id="513" class="Symbol">:</a>
  <a id="517" class="Symbol">{</a><a id="518" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#518" class="Bound">l1ᵉ</a> <a id="522" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#522" class="Bound">l2ᵉ</a> <a id="526" class="Symbol">:</a> <a id="528" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="533" class="Symbol">}</a> <a id="535" class="Symbol">{</a><a id="536" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#536" class="Bound">Aᵉ</a> <a id="539" class="Symbol">:</a> <a id="541" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="545" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#518" class="Bound">l1ᵉ</a><a id="548" class="Symbol">}</a> <a id="550" class="Symbol">{</a><a id="551" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#551" class="Bound">Bᵉ</a> <a id="554" class="Symbol">:</a> <a id="556" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="560" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#522" class="Bound">l2ᵉ</a><a id="563" class="Symbol">}</a> <a id="565" class="Symbol">→</a> <a id="567" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#536" class="Bound">Aᵉ</a> <a id="570" class="Symbol">→</a> <a id="572" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#551" class="Bound">Bᵉ</a> <a id="575" class="Symbol">→</a> <a id="577" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#394" class="Function">productᵉ</a> <a id="586" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#536" class="Bound">Aᵉ</a> <a id="589" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#551" class="Bound">Bᵉ</a>
<a id="592" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#506" class="Function">pair&#39;ᵉ</a> <a id="599" class="Symbol">=</a> <a id="601" href="foundation.dependent-pair-types%25E1%25B5%2589.html#679" class="InductiveConstructor">pairᵉ</a>

<a id="608" class="Keyword">infixr</a> <a id="615" class="Number">15</a> <a id="618" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">_×ᵉ_</a>
<a id="_×ᵉ_"></a><a id="623" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">_×ᵉ_</a> <a id="628" class="Symbol">:</a> <a id="630" class="Symbol">{</a><a id="631" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#631" class="Bound">l1ᵉ</a> <a id="635" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#635" class="Bound">l2ᵉ</a> <a id="639" class="Symbol">:</a> <a id="641" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="646" class="Symbol">}</a> <a id="648" class="Symbol">(</a><a id="649" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#649" class="Bound">Aᵉ</a> <a id="652" class="Symbol">:</a> <a id="654" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="658" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#631" class="Bound">l1ᵉ</a><a id="661" class="Symbol">)</a> <a id="663" class="Symbol">(</a><a id="664" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#664" class="Bound">Bᵉ</a> <a id="667" class="Symbol">:</a> <a id="669" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="673" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#635" class="Bound">l2ᵉ</a><a id="676" class="Symbol">)</a> <a id="678" class="Symbol">→</a> <a id="680" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="684" class="Symbol">(</a><a id="685" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#631" class="Bound">l1ᵉ</a> <a id="689" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="691" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#635" class="Bound">l2ᵉ</a><a id="694" class="Symbol">)</a>
<a id="696" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">_×ᵉ_</a> <a id="701" class="Symbol">=</a> <a id="703" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#394" class="Function">productᵉ</a>
</pre>
### The induction principle for the cartesian product type

<pre class="Agda"><a id="ind-productᵉ"></a><a id="785" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#785" class="Function">ind-productᵉ</a> <a id="798" class="Symbol">:</a>
  <a id="802" class="Symbol">{</a><a id="803" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#803" class="Bound">l1ᵉ</a> <a id="807" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#807" class="Bound">l2ᵉ</a> <a id="811" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#811" class="Bound">l3ᵉ</a> <a id="815" class="Symbol">:</a> <a id="817" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="822" class="Symbol">}</a> <a id="824" class="Symbol">{</a><a id="825" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#825" class="Bound">Aᵉ</a> <a id="828" class="Symbol">:</a> <a id="830" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="834" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#803" class="Bound">l1ᵉ</a><a id="837" class="Symbol">}</a> <a id="839" class="Symbol">{</a><a id="840" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#840" class="Bound">Bᵉ</a> <a id="843" class="Symbol">:</a> <a id="845" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="849" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#807" class="Bound">l2ᵉ</a><a id="852" class="Symbol">}</a> <a id="854" class="Symbol">{</a><a id="855" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#855" class="Bound">Cᵉ</a> <a id="858" class="Symbol">:</a> <a id="860" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#825" class="Bound">Aᵉ</a> <a id="863" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a> <a id="866" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#840" class="Bound">Bᵉ</a> <a id="869" class="Symbol">→</a> <a id="871" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="875" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#811" class="Bound">l3ᵉ</a><a id="878" class="Symbol">}</a> <a id="880" class="Symbol">→</a>
  <a id="884" class="Symbol">((</a><a id="886" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#886" class="Bound">xᵉ</a> <a id="889" class="Symbol">:</a> <a id="891" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#825" class="Bound">Aᵉ</a><a id="893" class="Symbol">)</a> <a id="895" class="Symbol">(</a><a id="896" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#896" class="Bound">yᵉ</a> <a id="899" class="Symbol">:</a> <a id="901" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#840" class="Bound">Bᵉ</a><a id="903" class="Symbol">)</a> <a id="905" class="Symbol">→</a> <a id="907" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#855" class="Bound">Cᵉ</a> <a id="910" class="Symbol">(</a><a id="911" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#886" class="Bound">xᵉ</a> <a id="914" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="917" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#896" class="Bound">yᵉ</a><a id="919" class="Symbol">))</a> <a id="922" class="Symbol">→</a> <a id="924" class="Symbol">(</a><a id="925" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#925" class="Bound">tᵉ</a> <a id="928" class="Symbol">:</a> <a id="930" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#825" class="Bound">Aᵉ</a> <a id="933" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a> <a id="936" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#840" class="Bound">Bᵉ</a><a id="938" class="Symbol">)</a> <a id="940" class="Symbol">→</a> <a id="942" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#855" class="Bound">Cᵉ</a> <a id="945" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#925" class="Bound">tᵉ</a>
<a id="948" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#785" class="Function">ind-productᵉ</a> <a id="961" class="Symbol">=</a> <a id="963" href="foundation.dependent-pair-types%25E1%25B5%2589.html#880" class="Function">ind-Σᵉ</a>
</pre>
### The recursion principle for the cartesian product type

<pre class="Agda"><a id="rec-productᵉ"></a><a id="1043" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1043" class="Function">rec-productᵉ</a> <a id="1056" class="Symbol">:</a>
  <a id="1060" class="Symbol">{</a><a id="1061" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1061" class="Bound">l1ᵉ</a> <a id="1065" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1065" class="Bound">l2ᵉ</a> <a id="1069" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1069" class="Bound">l3ᵉ</a> <a id="1073" class="Symbol">:</a> <a id="1075" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1080" class="Symbol">}</a> <a id="1082" class="Symbol">{</a><a id="1083" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1083" class="Bound">Aᵉ</a> <a id="1086" class="Symbol">:</a> <a id="1088" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1092" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1061" class="Bound">l1ᵉ</a><a id="1095" class="Symbol">}</a> <a id="1097" class="Symbol">{</a><a id="1098" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1098" class="Bound">Bᵉ</a> <a id="1101" class="Symbol">:</a> <a id="1103" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1107" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1065" class="Bound">l2ᵉ</a><a id="1110" class="Symbol">}</a> <a id="1112" class="Symbol">{</a><a id="1113" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1113" class="Bound">Cᵉ</a> <a id="1116" class="Symbol">:</a> <a id="1118" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1122" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1069" class="Bound">l3ᵉ</a><a id="1125" class="Symbol">}</a> <a id="1127" class="Symbol">→</a>
  <a id="1131" class="Symbol">(</a><a id="1132" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1083" class="Bound">Aᵉ</a> <a id="1135" class="Symbol">→</a> <a id="1137" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1098" class="Bound">Bᵉ</a> <a id="1140" class="Symbol">→</a> <a id="1142" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1113" class="Bound">Cᵉ</a><a id="1144" class="Symbol">)</a> <a id="1146" class="Symbol">→</a> <a id="1148" class="Symbol">(</a><a id="1149" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1083" class="Bound">Aᵉ</a> <a id="1152" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a> <a id="1155" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1098" class="Bound">Bᵉ</a><a id="1157" class="Symbol">)</a> <a id="1159" class="Symbol">→</a> <a id="1161" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1113" class="Bound">Cᵉ</a>
<a id="1164" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#1043" class="Function">rec-productᵉ</a> <a id="1177" class="Symbol">=</a> <a id="1179" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#785" class="Function">ind-productᵉ</a>
</pre>