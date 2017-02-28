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
If you are using Isabelle 2016-1, and have downloaded your AFP directory to
<code>/home/myself/afp</code>, you should run the following commands
<a href="#1">[1]</a> <a href="#2">[2]</a>:</p>
<p>
<pre class="code">
    mkdir -p ~/.isabelle/Isabelle2016-1/etc/
    echo "/home/myself/afp" >> ~/.isabelle/Isabelle2016-1/etc/components
</pre>

<p>
You can now refer to article <code>ABC</code> from the AFP in some theory of
yours via</p>

<pre class="code">
    imports "$AFP/ABC/Some_ABC_Theory"
</pre>

<p>This allows you to distribute your material separately from any AFP
theories. Users of your distribution also need to install the AFP in the above
manner.</p>


<p>
Note that referring to <strong>another AFP entry from inside an AFP
entry</strong> is different and much easier: 
<pre class="code">
    imports "../ABC/Some_ABC_Theory"
</pre>
For working inside the AFP, this is the mandated option.
It interacts correctly with multiple AFP installations side by side.
</p>
<p>You can also use this method in your own work outside the AFP, you only
need to place the AFP entries you refer to next to your development in the
correct location in the directory hierarchy.</p>
<p>
If you build on one other AFP entry, your ROOT file should make this explicit:
<pre>
session my_session = base_session +
</pre>
This avoids rerunning the <tt>base_session</tt> theories by building
on the <tt>base_session</tt> image instead. Thus running times of AFP
regression tests are reduced!
</p>

<p>&nbsp;</p>

<p>
<a name="1">[1]:</a> Tested for Linux and Mac installations &dash; it should be the same under cygwin on Windows.
</p>
<p>
<a name="2">[2]:</a> This is one method for installing the AFP as a component. Any other method for adding Isabelle components will work as well.</p>

    </td></tr>
  </tbody>
</table>
{% endblock %}

