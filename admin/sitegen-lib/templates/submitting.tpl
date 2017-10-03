{% extends "base.tpl" %}

{% block headline %}
<font class="first">S</font>ubmission
<font class="first">G</font>uidelines
{% endblock %}

{% block content %}
<table width="80%" class="descr">
  <tbody>
    <tr><td>

<p>Please send your submission
<a href="https://ci.isabelle.systems/afp-submission/">via this web page</a>.
</p>

<p><strong>The submission must follow the following Isabelle style rules.</strong>
    For additional guidelines on Isabelle proofs, also see the this <a href="http://proofcraft.org/blog/isabelle-style.html">guide</a> (feel free to follow all of these; only the below are mandatory).
    <strong>Technical details about the submission process and the format of the submission are explained on the submission site.</strong></p>
<ul>
    <li>No use of the commands <code>sorry</code> or <code>back</code>.</li>

    <li>Instantiations must not use Isabelle-generated names such as
    <code>xa</code> &mdash; use Isar, the <code>subgoal</code> command
    or <code>rename_tac</code> to avoid such names.</li>

    <li>No use of the command <code>smt_oracle</code>.</li>

    <li>If your theories contain calls to <code>nitpick</code> or
    <code>quickcheck</code>those calls must include the <code>expect</code>
    parameter. Alternatively the <code>expect</code> parameter must be set
    globally via
    <code>nitpick_params</code>/<code>quickcheck_params</code>.</li>

    <li><code>apply</code> scripts should be indented by subgoal as in
    the Isabelle distribution. If an <code>apply</code> command is
    applied to a state with <code>n+1</code> subgoals, it must be
    indented by <code>n</code> spaces relative to the first
    <code>apply</code> in the sequence.</li>

    <li>Only named lemmas should carry attributes such as <code>[simp]</code>.</li>

    <li>We prefer structured Isar proofs over apply style, but do not
    mandate them.</li>

    <li>If there are proof steps that take significant time, i.e. longer
    than roughly 1 min, please add a short comment to that step, so
    maintainers will know what to expect.</li>
</ul>

<p>It is possible and encouraged to build on other archive entries
   in your submission. There is a standardised way to 
   <a href="using.html">refer to other AFP entries</a> in your
   theories.</p>

<p>Your submission will be refereed and you will receive notification
as soon as possible. If accepted, you must agree to maintain your
archive entry or nominate someone else to maintain it. The Isabelle
development team will assist with maintenance, but it does not have the
resources to fully maintain the complete archive.</p>

<p>If you have questions regarding your submission, please email <a
href="&#109;&#97;&#105;&#108;&#116;&#111;:&#97;&#102;&#112;-&#115;&#117;&#98;&#109;&#105;&#116;&#64;&#105;&#110;&#46;&#116;&#117;&#109;&#46;&#100;&#101;">&#97;&#102;&#112;-&#115;&#117;&#98;&#109;&#105;&#116;&#64;&#105;&#110;&#46;&#116;&#117;&#109;&#46;&#100;&#101;</a>.
      If you need help with Isabelle, please use the
<a href="mailto:isabelle-users@cl.cam.ac.uk">isabelle-users@cl.cam.ac.uk</a>
      mailing list. It is always a good idea to <a
      href="https://lists.cam.ac.uk/mailman/listinfo/cl-isabelle-users">subscribe</a>.</p>

    </td></tr>
  </tbody>
</table>

{% endblock %}

