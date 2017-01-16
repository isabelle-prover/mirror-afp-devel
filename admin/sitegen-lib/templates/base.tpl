<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>{% block title %}Archive of Formal Proofs{% endblock %}</title>
<link rel="stylesheet" type="text/css" href="{{ ROOT_PATH }}front.css">
<link rel="icon" href="{{ ROOT_PATH }}images/favicon.ico" type="image/icon">
</head>

<body>
{#TODO remove width tags #}
{#TODO remove p blocks #}

<table width="100%">
<tbody>
<tr>

<!-- Navigation -->
<td width="20%" align="center" valign="top">
  <p>&nbsp;</p>
  <a href="http://isabelle.in.tum.de">
    <img src="{{ ROOT_PATH }}images/isabelle.png" width="100" height="86" border=0>
  </a>
  <p>&nbsp;</p>
  <p>&nbsp;</p>
  <table class="nav" width="80%">
    <tr>
      <td class="nav" width="100%"><a href="{{ ROOT_PATH }}index.shtml">Home</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}about.shtml">About</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}submitting.shtml">Submission Guidelines</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}updating.shtml">Updating entries</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}using.shtml">Using entries</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}search.shtml">Search</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}statistics.shtml">Statistics</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}topics.shtml">Index</a></td>
    </tr>
    <tr>
      <td class="nav"><a href="{{ ROOT_PATH }}download.shtml">Download</a></td>
    </tr>
  </table>
  <p>&nbsp;</p>
  <p>&nbsp;</p>
</td>


<!-- Content -->
<td width="80%" valign="top">
<div align="center">
  <p>&nbsp;</p>
  <h1>{% block headline %}{% endblock %}</h1>
  <p>&nbsp;</p>

{% block content %}
{% endblock %}

</div>
</td>

</tr>
</tbody>
</table>

{% block footer %}
{% endblock %}

</body>
</html>
