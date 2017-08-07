{% extends "base.tpl" %}

{% block headline %}
<font class="first">D</font>ownload the <font class="first">A</font>rchive</h1>
{% endblock %}

{% block content %}
<table width="80%" class="descr">
<tbody>
{% if not is_devel %}
<tr><td class="head">
  <b>Current stable version</b> (for current Isabelle release):
</td></tr>
<tr></tr><td class="entry">
    <a href="release/afp-current.tar.gz">afp-current.tar.gz</a>
</td></tr>
{% endif %}

<tr><td class="head">Older stable versions:</td></tr>
<tr><td class="entry">
  Please use the <a href="http://sourceforge.net/projects/afp/files/">
    sourceforge download system</a>
  to access older versions of the archive.
</td></tr>

<tr><td class="head">Mercurial access:</td></tr>

<tr><td class="entry">
  At <a href="https://bitbucket.org/isa-afp/afp-devel/">Bitbucket</a>
</td></tr>

<tr><td class="head">How to refer to AFP entries:</td></tr>
<tr><td class="entry">
  You can refer to AFP entries by using the <a href="using.html">AFP as an Isabelle component</a>.</td></tr>

</tbody></table>
{% endblock %}

