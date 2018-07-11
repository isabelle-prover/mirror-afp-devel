{% extends "base.tpl" %}

{% block headline %}
<font class="first">R</font>eferring to
<font class="first">A</font>FP
<font class="first">E</font>ntries
{% endblock %}

{% block content %}
<table width="80%" class="descr">
  <tbody>
    <tr><td>

<p>
Once you have downloaded the AFP, you can include its articles and theories in
your own developments. If you would like to make your work available to others
<i>without</i> having to include the AFP articles you depend on, here is how to do it.
</p>
<p>
If you are using Isabelle 2017, and have downloaded your AFP directory to
<code>/home/myself/afp</code>, you should run the following command
<a href="#1">[1]</a> to make the AFP session ROOTS available to Isabelle:</p>
<p>
<pre class="code">
    echo "/home/myself/afp/thys" >> ~/.isabelle/Isabelle2017/ROOTS
</pre>

<p>
You can now refer to article <code>ABC</code> from the AFP in some theory of
yours via</p>

<pre class="code">
    imports "ABC.Some_ABC_Theory"
</pre>

<p>This allows you to distribute your material separately from any AFP
theories. Users of your distribution also need to install the AFP in the above
manner.</p>

<p>&nbsp;</p>

<p>
<a name="1">[1]:</a> Tested for Linux and Mac installations &dash; it should be the same under cygwin on Windows.
</p>
<p>
    </td></tr>
  </tbody>
</table>
{% endblock %}

