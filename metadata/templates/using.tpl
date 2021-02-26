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
If you are using Isabelle2021, and have downloaded your AFP directory to
<code>/home/myself/afp</code>, for Linux/Mac you can run the following command to make the AFP session ROOTS available to Isabelle:</p>
<p>
<pre class="code">
    echo "/home/myself/afp/thys" >> ~/.isabelle/Isabelle2021/ROOTS
</pre>
This adds the path <code>/home/myself/afp/thys/</code> to the ROOTS file, which
Isabelle will scan by default. You can also manually edit and/or create that
ROOTS file. There are many other ways to achieve the same outcome, this is just
one option.
</p>
<p>
For Windows, the idea is the same just the path is slightly different. If the
AFP is in <code>C:\afp</code>, you should be able to run the following in a
Cygwin terminal.
<pre class="code">
    echo "/cygdrive/c/afp/thys" >> ~/.isabelle/Isabelle2021/ROOTS
</pre>
</p>

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

    </td></tr>
  </tbody>
</table>
{% endblock %}

