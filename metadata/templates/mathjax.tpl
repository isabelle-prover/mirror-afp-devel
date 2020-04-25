<!-- MathJax for LaTeX support in abstracts -->
{#
  The following is the MathJax configuration.
  This means that formulae can be enclosed in either $ … $ or \( … \)
#}
<script>
MathJax = {
  tex: {
    inlineMath: [['$', '$'], ['\\(', '\\)']]
  },
  processEscapes: true,
  svg: {
    fontCache: 'global'
  }
};
</script>
{# The following uses MathJax from their CDN #}
<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
{# The following uses our local copy of MathJax #}
{#<script id="MathJax-script" async src="{{ ROOT_PATH }}components/mathjax/es5/tex-mml-chtml.js"></script>#}

